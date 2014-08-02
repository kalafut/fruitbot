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

//shims = require("./shims.js");
//trace = shims.trace;
//EAST = shims.EAST;
//NORTH = shims.NORTH;
//WEST = shims.WEST;
//SOUTH = shims.SOUTH;
//TAKE = shims.TAKE;
//PASS = shims.PASS;

var on_server;
var debug = 1;

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

var ns = (function () {
    "use strict";
    var MY = 0, OPP = 1, num_cells, num_types, x_delta, y_delta, pass, Board, num_item_types,
        max_depth = 4, nodes_searched, nodeCheckThreshold, time_is_up = false, halfFruit, startTime, move_idx,
        START = 0, COMPLETE = 1, SKIP = 2, moveTrans, evalCache, xlat,timeCheckDelay = 500, fruitValue, wonTiedCats;

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
            Board.lastMove = [];
            Board.initialFruitLocations = [];
            Board.northLimit = HEIGHT;
            Board.southLimit = 0;
            Board.westLimit = WIDTH;
            Board.eastLimit = 0;

            for (i = 0; i < WIDTH; i += 1) {
                Board.board[i] = [];
                for (j = 0; j < HEIGHT; j += 1) {
                    Board.board[i][j] = start_board[i][j];
                    if (start_board[i][j] > 0) {
                        Board.initialFruitLocations.push({x:i, y:j});
                        Board.northLimit = Math.min(Board.northLimit, j);
                        Board.southLimit = Math.max(Board.southLimit, j);
                        Board.westLimit = Math.min(Board.westLimit, i);
                        Board.eastLimit = Math.max(Board.eastLimit, i);
                    }
                }
            }

            Board.history = [];

            Board.collected = [[], []];
            for (i = 1; i <= num_item_types; i += 1) {
                Board.collected[MY][i] = get_my_item_count(i);
                Board.collected[OPP][i] = get_opponent_item_count(i);
            }

            Board.loc = [];

            Board.loc[MY] = { x: get_my_x(), y: get_my_y() };
            Board.loc[OPP] = { x: get_opponent_x(), y: get_opponent_y() };
        },
        processMove: function (move) {
            var X, Y, undo, loc, loc_other, fruitType, amt, test_undo;

            loc = Board.loc[Board.side];
            loc_other = Board.loc[1 - Board.side];
            undo = { loc: { x: loc.x, y: loc.y }, move: move };


            /*
                pendingTake: Board.pendingTake,
                myCollected: Board.collected[MY].slice(0),
                oppCollected: Board.collected[OPP].slice(0),
                boardFruitChange:
            };*/

            if (move === TAKE) {
                fruitType = Board.board[loc.x][loc.y];
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
                    fruitType = Board.board[loc.x][loc.y];
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
                        Board.board[undo.loc.x][undo.loc.y] = undo.fruitType;
                        Board.pendingTake = true;
                    } else {
                        Board.collected[Board.side][undo.fruitType] -= 0.5;
                        Board.board[undo.loc.x][undo.loc.y] = undo.fruitType;
                        Board.pendingTake = true;
                    }
                } else {
                    Board.collected[other_side][undo.fruitType] -= 1;
                    Board.board[undo.loc.x][undo.loc.y] = undo.fruitType;
                }
            }

            Board.side = other_side;
        },

        movegen: function (moveLimiting) {
            var moves, gen, x, y, loc, l1, l2;

            loc = Board.loc[Board.side];
            x = loc.x;
            y = loc.y;

            moves = [];
            if (Board.history != undefined && Board.history.length > 2) {
                l1 = Board.history[Board.history.length - 1].move;
                l2 = Board.history[Board.history.length - 2].move;
            }

            if (moveLimiting && l1 != undefined && l2 != undefined && l1 != TAKE && l2 != TAKE) {
                if (Board.board[x][y] > 0) {
                    moves.push(TAKE);
                }
                if (x > Board.westLimit && (l2 == WEST || l2 == NORTH || l2 == SOUTH)) {
                    moves.push(WEST);
                }
                if (x < Board.eastLimit && (l2 == EAST || l2 == NORTH || l2 == SOUTH)) {
                    moves.push(EAST);
                }
                if (y > Board.northLimit && l2 == NORTH) {
                    moves.push(NORTH);
                }
                if (y < Board.southLimit && l2 == SOUTH) {
                    moves.push(SOUTH);
                }
            } else {
                if (Board.board[x][y] > 0) {
                    moves.push(TAKE);
                }
                if (x > Board.westLimit) {
                    moves.push(WEST);
                }
                if (x < Board.eastLimit) {
                    moves.push(EAST);
                }
                if (y > Board.northLimit) {
                    moves.push(NORTH);
                }
                if (y < Board.southLimit) {
                    moves.push(SOUTH);
                }
            }
            if (moves.length == 0) {
                moves.push(PASS);
            }
            return moves;
        },
        key: function () {
            var i, j, s="";

            for (i=1; i <= num_item_types; i++) {
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
            var h1, h2, h3, i;

            h1 = (Board.loc[MY].x << 12) |
                 (Board.loc[MY].y << 8) |
                 (Board.loc[OPP].x << 4) |
                 (Board.loc[OPP].y);

            for (i = 1; i <= num_item_types; i++ ) {
                h2 = Board.collected[MY][i] << (i*5);
                h3 = Board.collected[OPP][i] << (i*5 + 1);
            }

            return h1 ^ h2 ^ h3;
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


    function calc_score(board) {
        var score, material, i, types, row, col, dx, dy, dist, minDist, myLoc, oppLoc, tiedCats = 0,
            myPositionValue, oppPositionValue, myCats = 0, oppCats = 0, cell, myCollected, oppCollected;

        nodes_searched += 1;

        myCollected = Board.collected[Board.side];
        oppCollected = Board.collected[1 - Board.side];
        myLoc = Board.loc[Board.side];
        oppLoc = Board.loc[1 - Board.side];

        // First award categories won
        for (i = 1; i <= num_item_types; i += 1) {
            if (myCollected[i] > halfFruit[i]) {
                myCats += 1;
                wonTiedCats[i] = true;
            } else if (oppCollected[i] > halfFruit[i]) {
                oppCats += 1;
                wonTiedCats[i] = true;
            } else if(myCollected[i] == halfFruit[i] && oppCollected[i] == halfFruit[i]) {
                tiedCats += 1;
                wonTiedCats[i] = true;
            } else {
                wonTiedCats[i] = false;
            }

        }

        if (myCats > num_item_types / 2) {
            return Infinity;
        } else if (oppCats > num_item_types / 2) {
            return -Infinity;
        }

        if(myCats + oppCats + tiedCats == num_item_types) {
            if(myCats > oppCats) {
                return Infinity;
            } else if(myCats < oppCats) {
                return -Infinity;
            }
        }

        // Compute fruit values
        for (i = 1; i <= num_item_types; i += 1) {
            if(!wonTiedCats[i]) {
                fruitValue[i] = 100 / (halfFruit[i] + 0.5 - Math.max(myCollected[i], oppCollected[i]));
            } else {
                fruitValue[i] = 0;
            }
        }

        // Compute position value
        myPositionValue = 0;
        oppPositionValue = 0;
        for (i=0; i < board.initialFruitLocations.length; i++) {
            col = board.initialFruitLocations[i].x;
            row = board.initialFruitLocations[i].y;

            cell = board.board[col][row];
            if (cell > 0 && !wonTiedCats[cell]) {
                dx = col - myLoc.x;
                dy = row - myLoc.y;
                dist = Math.abs(dx) + Math.abs(dy);

                myPositionValue += fruitValue[cell] / (dist + 1);

                dx = col - oppLoc.x;
                dy = row - oppLoc.y;
                dist = Math.abs(dx) + Math.abs(dy);

                oppPositionValue += fruitValue[cell] / (dist + 1);
            }
        }

        material = 0;
        for (i = 1; i <= num_item_types; i += 1) {
            if (!wonTiedCats[i]) {
                material += fruitValue[i] * myCollected[i] - fruitValue[i] * oppCollected[i];
            }
        }

        score = 1000 * (myCats - oppCats) + material + 0.1 * (myPositionValue - oppPositionValue);

        return score;
    }

    function negamax(board, sd, depth, alpha, beta, moveOrder, startTime, maxTimeMS) {
        var ret_val, moves, i, j, val, best_move, best_score, prune, hash1, hash2, max;
        var boardHash, cacheEval, moveList;


        if(depth === sd) {
            moveList = [];
        }

        max = -Infinity;
        if (timeCheckDelay < 0) {
            if ((new Date()) - startTime > maxTimeMS) {
                time_is_up = true;
            } else {
                timeCheckDelay = 750;
            }
        } else {
            timeCheckDelay--;
        }

        if (!time_is_up) {
            if (depth === 0) {
                max = calc_score(board);
            } else {
                prune = false;
                if (moveOrder === undefined) {
                    moves = board.movegen(true);
                } else {
                    moves = moveOrder;
                }
                best_move = moves[0];

                for (i = 0; i < moves.length && !time_is_up && !prune; i += 1) {
                    board.processMove(moves[i]);
                    val = negamax(board, sd, depth - 1, -beta, -alpha, undefined, startTime, maxTimeMS);

                    if (val !== undefined) {
                        val.score *= -1;
                    } else {
                        break;
                    }
                    board.undoMove();

                    if (depth === sd) {
                        moveList.push({ move: moves[i], score: val.score });
                    }


                    if (val.score > max) {
                        max = val.score;
                        best_move = moves[i];
                    }

                    if (val.score > alpha) {
                        alpha = val.score;
                    }

                    if (alpha >= beta) {
                        max = alpha;
                        prune = true;
                    }
                }
            }

            ret_val = { move: best_move, score: max, moveList: moveList };
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
            if (move !== undefined) {
                bestMove = move;
                dbg_trace("Best move: " + move.move);

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

            currentDepth += 2;
        }
        for(i = 0; i < bestMove.moveList.length; i++) {
            trace("Move: " + xlat[bestMove.moveList[i].move] + "  Score: " + bestMove.moveList[i].score);
        }
        trace((currentDepth - 2).toString() + " ply / " + nodes_searched.toString() + " nodes / " +(((new Date()) - startTime)/1000).toString() + "s" );

        return bestMove;

    }

    function new_game() {
        var col, row, moves, i;

        num_cells = WIDTH * HEIGHT;
        num_item_types = get_number_of_item_types();

        // Compute half fruit thresholds
        halfFruit = [];
        for (i = 1; i <= num_item_types; i += 1) {
            halfFruit[i] = get_total_item_count(i) / 2;
        }

        fruitValue = new Array(num_item_types + 1),
        wonTiedCats = new Array(num_item_types + 1);
    }

    function make_move(time) {
        var board, best_move, fruit_goal, i, move, start;

        startTime = new Date();

        Board.init(get_board());

        nodes_searched = 0;
        move = search_mgr(Board, 2, time);
        trace(nodes_searched * 1000 / ((new Date()) - startTime));

        return move.move;
    }


    return { new_game: new_game, make_move: make_move };

}());



function make_move(time) {
    "use strict";
    if (time === undefined) {
        time = on_server ? 9900 : 1000;
    }
    return ns.make_move(time);
}

function new_game() {
    "use strict";
    ns.new_game();
}

// Optionally include this function if you'd like to always reset to a 
// certain board number/layout. This is useful for repeatedly testing your
// bot(s) against known positions.
//
function default_board_number() {
    return 571395;
}

function default_board_setup() {
    //return t1();
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

function b836151() {
    var setup = {
        width: 12,
        height: 12,
                //  Apple, Banana, Cherry, Me, Orange
        myFruit:    [ 1,     0,    3.5,    1.5,     2 ],
        oppFruit:   [ 0,     2,    1.5,    3.5,     5 ],
        board: [
            // 1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
            "+-----------------------------------------------------------+",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 1
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 2
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 3
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 4
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   | M |   |   |   |   |   |   |", // 5
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   | @ |   |   |   | M |   |   |   |   |", // 6
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 7
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   | B |   |   |   |   |   |   |   |", // 8
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   | O |   |   |   |   |   |", // 9
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 10
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   | O |   |   |   |   |   |   |   |   |   |", // 11
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   | % |   |   |   |   |   |   |   |   |   |   |", // 12
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
function b912619() {
    var setup = {
        width: 7,
        height: 7,
                //  Apple, Banana, Cherry, Me, Orange
        myFruit:    [ 0.5,     0.5,      1,      0,     0 ],
        oppFruit:   [ 0.5,     1.5,      1,      0,     0 ],
        board: [
            // 1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
            "+-----------------------------------------------------------+",
            "|   |   |   | C | @ |   | B |   |   |   |   |   |   |   |   |", // 1
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 2
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   | % |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 3
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 4
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 5
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "| C |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 6
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   | C |   |   |   |   |   |   |   |   |", // 7
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 8
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 9
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 10
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 11
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 12
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

function t1() {
    var setup = {
        width: 6,
        height: 6,
                //  Apple, Banana, Cherry, Me, Orange
        myFruit:    [ 0.5,   1.5,      2,      0,     0 ],
        oppFruit:   [ 0.5,   1.5,      1,      0,     0 ],
        board: [
            // 1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
            "+-----------------------------------------------------------+",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 1
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 2
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   | @ |   |   |   |   |   |   |   |   |   |   |", // 3
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   | C |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 4
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |C% |   |   |   |   |   |   |   |   |   |   |   |", // 5
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 6
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 7
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 8
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 9
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 10
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 11
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 12
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
function blank() {
    var setup = {
        width: 13,
        height: 13,
                //  Apple, Banana, Cherry, Me, Orange
        myFruit:    [ 0,     0,      0,      0,     0 ],
        oppFruit:   [ 0,     0,      0,      0,     0 ],
        board: [
            // 1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
            "+-----------------------------------------------------------+",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 1
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 2
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 3
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 4
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 5
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   | @ |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 6
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "| % |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 7
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 8
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 9
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 10
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 11
            "+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---|",
            "|   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |", // 12
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

