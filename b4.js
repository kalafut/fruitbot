/*global WIDTH, HEIGHT, get_number_of_item_types, get_my_x, get_my_y, get_opponent_x, get_opponent_y, EAST, NORTH, WEST, SOUTH, TAKE, PASS */
/*global get_board, get_total_item_count, get_my_item_count, get_opponent_item_count, trace */

/* Goals
 *
 * Rewrite as a alternating move system to support negamax
 * Return best move found from interrupted searches
 * Proper alpha-beta pruning
 *
 * Clean take:
 *   Record fruit type, amount as 1.0, add 1.0 to player, remove from board
 * Clean undo:
 *   Subtract 1.0 from player, add to board
 *
 * Shared Take Start:
 *   Record fruit type, amount as 0.5, add 0.5 to player A, set pending take, leave on board
 *
 * Shared Take Complete:
 *   Record fruit type, amount as 0.5, add 0.5 to player B, remove from board
 *
 * Shared Take Declined
 */



try {
    window;
    on_server = false;
    trace("local");
} catch(e) {
    on_server = true;
    debug = false;
    trace("server");
}

function dbg_trace(s) {
    if (debug) {
        trace(s);
    }
}

var ns_b4 = (function () {
    "use strict";
    var MY = 0, OPP = 1, num_cells, num_types, x_delta, y_delta, pass, Board, num_item_types,
        max_depth = 4, nodes_searched, nodeCheckThreshold, time_is_up = false, halfFruit, startTime, move_idx,
        START = 0, COMPLETE = 1, SKIP = 2, moveTrans, moveHist, evalCache, xlat;

    moveTrans = { NORTH: 'N', SOUTH: 'S', EAST: 'E', WEST: 'W', TAKE: 'T', PASS: 'P' };

    xlat = [];
    xlat[EAST] = "EAST";
    xlat[NORTH] = "NORTH";
    xlat[WEST] = "WEST";
    xlat[SOUTH] = "SOUTH";
    xlat[TAKE] = "TAKE";
    xlat[PASS] = "PASS";


    Board = {
        init: function (start_board) {
            var i, j, x, y;

            evalCache = {};
            // initialize board
            Board.board = [];
            Board.move_num = 0;
            Board.side = MY;
            Board.lastMove = {};
            Board.pendingTake = false;
            Board.moveHist = "";

            for (i = 0; i < WIDTH; i += 1) {
                Board.board[i] = [];
                for (j = 0; j < HEIGHT; j += 1) {
                    Board.board[i][j] = start_board[i][j];
                }
            }

            Board.history = [];

            Board.collected = [[], []];
            for (i = 0; i < get_number_of_item_types(); i += 1) {
                Board.collected[MY][i] = get_my_item_count(i + 1);
                Board.collected[OPP][i] = get_opponent_item_count(i + 1);
            }

            Board.loc = [];

            Board.loc[MY] = { x: get_my_x(), y: get_my_y() };
            Board.loc[OPP] = { x: get_opponent_x(), y: get_opponent_y() };
        },
        processMove: function (move) {
            var X, Y, undo, loc, loc_other, fruitType, amt, test_undo;

            loc = Board.loc[Board.side];
            loc_other = Board.loc[1 - Board.side];
            undo = { loc: { x: loc.x, y: loc.y } };
            Board.moveHist += moveTrans[move];
            /*
                pendingTake: Board.pendingTake,
                myCollected: Board.collected[MY].slice(0),
                oppCollected: Board.collected[OPP].slice(0),
                boardFruitChange:
            };*/

            if (move === TAKE) {
                fruitType = Board.board[loc.x][loc.y] - 1;
                undo.fruitType = fruitType;
                if (!Board.pendingTake) {
                    // We only to the 0.5 take if it's side 0. If it is side 1 and the locations
                    // are the same, it just means side 0 moved to that square as part of the same
                    // turn, so side 1 is entitle to the full fruit. An artifact of splitting
                    // simultaneous moves into turn based.
                    if (loc.x === loc_other.x && loc.y === loc_other.y && Board.side === 0) {
                        Board.collected[Board.side][fruitType] += 0.5;
                        Board.pendingTake = true;
                        undo.sharedTake = START;
                    } else {
                        Board.collected[Board.side][fruitType] += 1;
                        Board.board[loc.x][loc.y] = 0;
                    }
                } else {
                    Board.collected[Board.side][fruitType] += 0.5;
                    Board.board[loc.x][loc.y] = 0;
                    Board.pendingTake = false;
                    undo.sharedTake = COMPLETE;
                }
            } else {
                if (move !== TAKE && Board.pendingTake) {
                    fruitType = Board.board[loc.x][loc.y] - 1;
                    Board.collected[1 - Board.side][fruitType] += 0.5;
                    Board.board[loc.x][loc.y] = 0;
                    undo.fruitType = fruitType;
                    undo.sharedTake = SKIP;
                }
                if (move === NORTH) {
                    Board.loc[Board.side].y -= 1;
                } else if (move === SOUTH) {
                    Board.loc[Board.side].y += 1;
                } else if (move === EAST) {
                    Board.loc[Board.side].x += 1;
                } else if (move === WEST) {
                    Board.loc[Board.side].x -= 1;
                }
                Board.pendingTake = false;
            }
            Board.history.push(undo);
            Board.move_num += 1;
            Board.side = 1 - Board.side;
        },
        undoMove: function () {
            var other_side = 1 - Board.side, undo;

            undo = Board.history.pop();
            Board.move_num -= 1;
            Board.loc[other_side] = undo.loc;

            if (undo.fruitType !== undefined) {
                if (undo.sharedTake !== undefined) {
                    if (Board.pendingTake) {
                        Board.collected[other_side][undo.fruitType] -= 0.5;
                        Board.pendingTake = false;
                    } else if (undo.sharedTake === COMPLETE) {
                        Board.collected[other_side][undo.fruitType] -= 0.5;
                        Board.board[undo.loc.x][undo.loc.y] = undo.fruitType + 1;
                        Board.pendingTake = true;
                    } else {
                        Board.collected[Board.side][undo.fruitType] -= 0.5;
                        Board.board[undo.loc.x][undo.loc.y] = undo.fruitType + 1;
                        Board.pendingTake = true;
                    }
                } else {
                    Board.collected[other_side][undo.fruitType] -= 1;
                    Board.board[undo.loc.x][undo.loc.y] = undo.fruitType + 1;
                }
            }
            Board.moveHist = Board.moveHist.slice(0,-1);

            Board.side = other_side;
        },

        movegen: function () {
            var moves, gen;

            gen = function (loc) {
                var x = loc.x,
                    y = loc.y,
                    moves = []; // PASS is probably a waste of search time

                if (Board.board[x][y] > 0) {
                    moves.push(TAKE);
                }
                if (x > 0) {
                    moves.push(WEST);
                }
                if (x < WIDTH - 1) {
                    moves.push(EAST);
                }
                if (y > 0) {
                    moves.push(NORTH);
                }
                if (y < HEIGHT - 1) {
                    moves.push(SOUTH);
                }
                return moves;
            };

            moves = gen(Board.loc[Board.side]);

            return moves;
        },
        key: function () {
            var i, j, s="";

            for (i=0; i < num_item_types; i++) {
                s += "A+" + Board.collected[MY][i].toString();
                s += "B+" + Board.collected[OPP][i].toString();
            }
            for (i=0; i < WIDTH; i++) {
                for (j=0; j < HEIGHT; j++) {
                    s += "C+" + Board.board[i][j].toString();
                }
            }

            s += "D+" + Board.loc[MY].x;
            s += "D+" + Board.loc[MY].y;
            s += "E+" + Board.loc[OPP].x;
            s += "E+" + Board.loc[OPP].y;

            return s;
        },
        hash: function() {
            return Board.moveHist;
        }
    };

    function reduce_board(board) {
        var new_board = [], col, row, t, total;
        for (col = 0; col < WIDTH; col += 1) {
            new_board[col] = [];
        }

        for (row = 0; row < HEIGHT; row += 1) {
            for (col = 0; col < WIDTH; col += 1) {
                new_board[col][row] = board[col][row];
                if (new_board[col][row] > 0) {
                    t = new_board[col][row];
                    total = get_total_item_count(t);
                    if (get_my_item_count(t) / total > 0.5 || get_opponent_item_count(t) / total > 0.5) {
                        new_board[col][row] = 0;
                    }
                }
            }
        }
        return new_board;
    }

    function gravity(board) {
        var force, theta, dx, dy, dist, tx, ty, d, move,
            mx = get_my_x(), my = get_my_y(), row, col,
            vector = {
                theta: 0,
                r: 0
            };
        for (row = 0; row < HEIGHT; row += 1) {
            for (col = 0; col < WIDTH; col += 1) {
                if (board[col][row] > 0) {
                    dx = col - mx;
                    dy = row - my;
                    dist = Math.sqrt(Math.pow(dx, 2) + Math.pow(dy, 2));
                    if (dist === 0) {
                        return TAKE;
                    }

                    force = 1 / Math.pow(dist, 2);
                    theta = Math.atan2(-dy, dx);
                    tx = vector.r * Math.cos(vector.theta);
                    ty = vector.r * Math.sin(vector.theta);
                    tx += force * Math.cos(theta);
                    ty += force * Math.sin(theta);
                    vector.r = Math.sqrt(Math.pow(tx, 2) + Math.pow(ty, 2));
                    vector.theta = Math.atan2(ty, tx);
                }
            }
        }
        d = vector.theta;
        if (d <= Math.PI / 4 && d > -Math.PI / 4) {
            move =  EAST;
        } else if (d >= Math.PI / 4 && d < 3 * Math.PI / 4) {
            move =  NORTH;
        } else if (d >= 3 * Math.PI / 4 || d <= -3 * Math.PI / 4) {
            move =  WEST;
        } else {
            move = SOUTH;
        }

        return move;

    }

    function calc_score(board) {
        var score, material, i, types, row, col, dx, dy, dist, minDist, myLoc, oppLoc,
            myCats = 0, oppCats = 0, wonCats = [], cell, myCollected, oppCollected;
        var points = {
            win: Infinity,
            lose: -Infinity
        };

        nodes_searched += 1;
        //if (nodes_searched % 10000 == 0) { trace(nodes_searched.toString()); }

        myCollected = Board.collected[Board.side];
        oppCollected = Board.collected[1 - Board.side];
        myLoc = Board.loc[Board.side];
        oppLoc = Board.loc[1 - Board.side];

        // First award categories won
        for (i = 0; i < num_item_types; i += 1) {
            if (myCollected[i] > halfFruit[i]) {
                myCats += 1;
                wonCats.push(i);
            } else if (oppCollected[i] > halfFruit[i]) {
                oppCats += 1;
                wonCats.push(i);
            }
        }

        if (myCats > num_item_types / 2) {
            return points.win;
        } else if (oppCats > num_item_types / 2) {
            return points.lose;
        }

        minDist = { my: 9999, opp: 9999 };
        for (row = 0; row < HEIGHT; row += 1) {
            for (col = 0; col < WIDTH; col += 1) {
                cell = board.board[col][row];
                if (cell > 0 && wonCats.indexOf(cell - 1) === -1) {
                    dx = col - myLoc.x;
                    dy = row - myLoc.y;
                    dist = Math.abs(dx) + Math.abs(dy);

                    if (dist < minDist.my) {
                        minDist.my = dist;
                    }
                    dx = col - oppLoc.x;
                    dy = row - oppLoc.y;
                    dist = Math.abs(dx) + Math.abs(dy);

                    if (dist < minDist.opp) {
                        minDist.opp = dist;
                    }
                }
            }
        }
        if (minDist.my === 9999) {
            minDist.my = 0;
        }
        if (minDist.opp === 9999) {
            minDist.opp = 0;
        }

        material = 0;
        for (i = 0; i < num_item_types; i += 1) {
            if (wonCats.indexOf(i) === -1) {
                material += myCollected[i] - oppCollected[i];
            }
        }

        score = 5 * (myCats - oppCats) + material - 0.05 * (minDist.my - minDist.opp);

        return score;
    }

    function negamax(board, sd, depth, alpha, beta, moveOrder, startTime, maxTimeMS) {
        var ret_val, moves, i, j, val, best_move, best_line, best_score, prune, hash1, hash2, max;
        var boardHash, cacheEval, moveList;


        if(depth === sd) {
            moveList = [];
        }

        max = -Infinity;
        best_line = [];
        if (nodes_searched > nodeCheckThreshold) {
            if ((new Date()) - startTime > maxTimeMS) {
                time_is_up = true;
            } else {
                nodeCheckThreshold = nodes_searched + 2000;
            }
        }

        if (!time_is_up) {
            if (depth === 0) {
                max = calc_score(board);
            } else {
                prune = false;
                if (moveOrder === undefined) {
                    moves = board.movegen();
                } else {
                    moves = moveOrder;
                }
                best_move = moves[0];
                //if(depth === sd && moveOrder !== undefined) {
                //    moves = moveOrder;
                //}

                for (i = 0; i < moves.length && !time_is_up && !prune; i += 1) {
                    //hash1 = board.key();
                    board.processMove(moves[i]);
                    /*
                    boardHash = board.hash();
                    cacheEval = evalCache[boardHash];

                    if (cacheEval !== undefined &&
                        cacheEval.depth >= depth - 1) {
                        val = cacheEval.eval;
                    } else {
                        val = negamax(board, sd, depth - 1, -beta, -alpha, moveOrder, startTime, maxTimeMS);
                        if (depth > 6) {
                            evalCache[boardHash] = { eval:val, depth: depth - 1};
                        }
                    }*/
                    val = negamax(board, sd, depth - 1, -beta, -alpha, undefined, startTime, maxTimeMS);

                    if (val !== undefined) {
                        val.score *= -1;
                        val.score -= 0.01 * (20 - depth);
                    } else {
                        break;
                    }
                    board.undoMove();

                    if (depth === sd) {
                        moveList.push({ move: moves[i], score: val.score });
                    }
                    //hash2 = board.key();
                    //if(hash1 !== hash2) {
                    //    alert('Undo error');
                    //}


                    if (val.score > max) {
                        max = val.score;
                        best_move = moves[i];
                        best_line = val.line;
                        //ret_val = { score: max, move: moves[i], line: val.line };
                    }

                    if (val.score > alpha) {
                        alpha = val.score;
                    }

                    if (alpha >= beta) {
                        max = alpha;
                        prune = true;
                    }

                }
                //if (ret_val === undefined) {
                //    ret_val = { score: max };
                //}
            }

            best_line.unshift(best_move);
            ret_val = { move: best_move, score: max, line: best_line, moveList: moveList };
        }

        if (time_is_up) {
            ret_val = undefined;
        }
        return ret_val;

    }


    function search_mgr(board, startDepth, time) {
        var currentDepth = startDepth, i,
            move, moveList, bestMove, exitNow = false;

        nodes_searched = 0;
        nodeCheckThreshold = 10000;
        time_is_up = false;
        bestMove = {};

        //move = negamax(board, 4, -99999, 99999, 1, startTime, 10000);
        while (!exitNow) {
            dbg_trace("Searching " + currentDepth);
            move = negamax(board, currentDepth, currentDepth, -99999, 99999, moveList, startTime, time);
            //move = negamax(board, currentDepth, currentDepth, -99999, 99999, undefined, startTime, 8000);
            if (move !== undefined) {
                bestMove = move;
                dbg_trace("Best move: " + move.move);
                //dbg_trace(bestMove.line.toString());

                if (bestMove.score == Infinity) {
                    trace("===Forced Win Found===");
                    exitNow = true;
                }

                move.moveList.sort( function(a,b) { return ( a.score >= b.score ) ? -1 : 1; } );
                moveList = [];
                for (i = 0; i < move.moveList.length; i++) {
                    moveList[i] = move.moveList[i].move;
                }
            } else {
                exitNow = true;
            }

            currentDepth += 1;
        }
        for(i = 0; i < bestMove.moveList.length; i++) {
            trace("Move: " + xlat[bestMove.moveList[i].move] + "  Score: " + bestMove.moveList[i].score);
        }
        trace((currentDepth - 1).toString() + " ply / " + nodes_searched.toString() + " nodes / " +(((new Date()) - startTime)/1000).toString() + "s" );
        //trace(bestMove.line.toString());

        return bestMove;

    }

    function new_game() {
        var col, row, moves;

        num_cells = WIDTH * HEIGHT;
        num_item_types = get_number_of_item_types();

        move_idx = [];
        for (col = 0; col < WIDTH; col += 1) {
            moves = [];
            move_idx[col] = moves;
            for (row = 0; row < HEIGHT; row += 1) {
                if (col > 0) {
                    moves.push(WEST);
                }
                if (col < WIDTH - 1) {
                    moves.push(EAST);
                }
                if (row > 0) {
                    moves.push(NORTH);
                }
                if (row < HEIGHT - 1) {
                    moves.push(SOUTH);
                }
            }
        }
    }

    function make_move(time) {
        var board, min_dist, best_move, fruit_goal, i, move, start;

        startTime = new Date();

        halfFruit = [];
        for (i = 0; i < num_item_types; i += 1) {
            halfFruit[i] = get_total_item_count(i + 1) / 2;
        }


        Board.init(get_board());
        min_dist = 9e99;


        nodes_searched = 0;
        move = search_mgr(Board, 2, time);
        trace(nodes_searched * 1000 / ((new Date()) - startTime));

        return move.move;
    }


    return { new_game: new_game, make_move: make_move };

}());


var B4 = {
    make_move: function(time) {
        "use strict";
        if (time === undefined) {
            time = on_server ? 9300 : 1000;
        }
        return ns_b4.make_move(time);
    },

    new_game: function() {
        "use strict";
        ns_b4.new_game();
    }
}

// Optionally include this function if you'd like to always reset to a 
// certain board number/layout. This is useful for repeatedly testing your
// bot(s) against known positions.
//
//function default_board_number() {
//    return 347610;
//}

//function default_board_setup() {
//    return b775902_2();
//}

function b757429_18() {
    var setup = {
        width: 13,
        height: 13,
                //  Apple, Banana, Cherry, Me, Orange
        myFruit:    [ 0,     0,      1,      0,     0 ],
        oppFruit:   [ 0,     0,      1,      0,     0 ],
        board: [
            // 1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
            "+-----------------------------------------------------------+",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 1
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   | C |   | B |   |   |   |   |   |   |", // 2
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 3
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 4
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 5
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "| A | B@|   |   |   |   |   |   |   | C |   |   |   |   |   |", // 6
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "| % |   |   |   |   |   |   |   |   | B |   |   |   |   |   |", // 7
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 8
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 9
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 10
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 11
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   | C |   |   |", // 12
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 13
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 14
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 15
            "+-----------------------------------------------------------+" ]
    };

    return setup;
}

function b775902_2() {
    var setup = {
        width: 12,
        height: 12,
                //  Apple, Banana, Cherry, Me, Orange
        myFruit:    [ 0,     0,      0,      0,     0 ],
        oppFruit:   [ 0,     0,      1,      0,     0 ],
        board: [
            // 1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
            "+-----------------------------------------------------------+",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 1
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "| M |   |   |   |   | O | O |   |   |   |   |   |   |   |   |", // 2
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   | B |   |   |   |   |   |   |   |", // 3
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   | M |   | O |   |   |   |   |   |   |", // 4
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   | O |   |   |   |   |   |   |   |   |   |", // 5
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   | O |   | B |   |   | C |   |   |   | M |   |   |   |   |", // 6
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   | B |   |   |   |%O@|   |   |   | B |   |   |   |   |   |", // 7
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   | M |   |   |   |   |   |   |   |   |   |   |", // 8
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   | C |   |   |   | A | O |   |   |   |   |   |   |   |   |", // 9
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   | M | M |   |   |   |   |   |   |", // 10
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   | M |   | C |   | O | C | O |   |   |   |   |   |   |", // 11
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   | C |   |   |   |   |   |   |   |   |   |   |", // 12
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 13
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 14
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 15
            "+-----------------------------------------------------------+" ]
    };

    return setup;
}
