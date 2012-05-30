/*global WIDTH, HEIGHT, get_number_of_item_types, get_my_x, get_my_y, get_opponent_x, get_opponent_y, EAST, NORTH, WEST, SOUTH, TAKE, PASS */
/*global get_board, get_total_item_count, get_my_item_count, get_opponent_item_count, trace */

/* Goals
 *
 * Rewrite as a alternating move system to support negamax
 * Return best move found from interrupted searches
 * Proper alpha-beta pruning
 */

var ns = (function () {
    "use strict";
    var MY = 0, OPP = 1, num_cells, num_types, x_delta, y_delta, pass, Board, num_item_types,
        max_depth = 4, nodes_searched, nodeCheckThreshold, time_is_up = false, halfFruit, startTime;


    Board = {
        init: function (start_board) {
            var i, j, x, y;

            // initialize board
            Board.board = [];
            Board.move_num = 0;
            Board.side = MY;
            Board.lastMove = {};
            Board.pendingTake = false;

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

            if (move === TAKE) {
                if (!Board.pendingTake) {
                    if (loc.x === loc_other.x && loc.y === loc_other.y) {
                        amt = 0.5;
                        Board.pendingTake = true;
                    } else {
                        amt = 1;
                    }
                    fruitType = Board.board[loc.x][loc.y] - 1;
                    Board.collected[Board.side][fruitType] += amt;
                    Board.board[loc.x][loc.y] -= amt;
                    undo.fruitChange = { fruitType: fruitType, amt: amt };
                } else {
                    fruitType = Board.board[loc.x][loc.y] - 0.5; // Because we already took half the fruit so the type if FUBAR
                    Board.collected[Board.side][fruitType] += 0.5;
                    Board.board[loc.x][loc.y] = 0;
                    undo.fruitChange = { fruitType: fruitType, amt: 0.5, doubleTake: true };
                    Board.pendingTake = false;
                }
            } else {
                if (move !== TAKE && Board.pendingTake) {
                    fruitType = Board.board[loc.x][loc.y] - 1;
                    Board.collected[1 - Board.side][fruitType] += 0.5;
                    Board.board[loc.x][loc.y] = 0;
                    undo.fruitChange = { fruitType: fruitType, amt: 0.5 };
                } else if (move === NORTH) {
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

            if (undo.fruitChange !== undefined) {
                if (undo.fruitChange.doubleTake) {
                    Board.collected[other_side][undo.fruitChange.fruitType] -= undo.fruitChange.amt;
                    Board.board[undo.loc.x][undo.loc.y] += undo.fruitChange.amt;
                } else {
                    Board.collected[other_side][undo.fruitChange.fruitType] -= undo.fruitChange.amt;
                    Board.board[undo.loc.x][undo.loc.y] += undo.fruitChange.amt;
                }
            }
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

                    /*
                       if(dist < min_dist) {
                       min_dist = dist;
                       if(Math.abs(dx) >= Math.abs(dy)) {
                    // Go EAST or WEST
                    if(dx > 0) {
                    best_move = EAST;
                    } else {
                    best_move = WEST;
                    }
                    } else {
                    if(dy > 0) {
                    best_move = SOUTH;
                    } else {
                    best_move = NORTH;
                    }
                    }
                    }
                    */
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
        var score, material, i, types, row, col, dx, dy, dist, min_dist, loc,
            myCats = 0, oppCats = 0, wonCats = [], cell, myCollected, oppCollected;

        nodes_searched += 1;

        myCollected = Board.collected[Board.side];
        oppCollected = Board.collected[1 - Board.side];
        loc = Board.loc[Board.side];

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

        min_dist = 9999;
        for (row = 0; row < HEIGHT; row += 1) {
            for (col = 0; col < WIDTH; col += 1) {
                cell = board.board[col][row];
                if (cell > 0 && wonCats.indexOf(cell - 1) === -1) {
                    dx = col - loc.x;
                    dy = row - loc.y;
                    dist = Math.abs(dx) + Math.abs(dy);

                    if (dist < min_dist) {
                        min_dist = dist;
                    }
                }
            }
        }
        if (min_dist === 9999) {
            min_dist = 0;
        }

        material = 0;
        for (i = 0; i < num_item_types; i += 1) {
            if (wonCats.indexOf(i) === -1) {
                material += myCollected[i] - oppCollected[i];
            }
        }

        score = 5 * (myCats - oppCats) + material - 0.01 * min_dist;

        return score;
    }

    function negamax(board, depth, alpha, beta, side, startTime, maxTimeMS) {
        var ret_val, moves, i, j, val, best_move, best_score, prune;

        if (nodes_searched > nodeCheckThreshold) {
            if ((new Date()) - startTime > maxTimeMS) {
                time_is_up = true;
            } else {
                nodeCheckThreshold = nodes_searched + 10000;
            }
        }

        if (!time_is_up) {
            if (depth === 0) {
                ret_val = { score: side * calc_score(board) };
            } else {
                prune = false;
                moves = board.movegen();

                for (i = 0; i < moves.length && !time_is_up && !prune; i += 1) {
                    board.processMove(moves[i]);
                    val = negamax(board, depth - 1, -beta, -alpha, -side, startTime, maxTimeMS);
                    val.score *= -1;
                    if (depth === 4) {
                        trace("My move:" + moves[i] + " score: " + val.score);
                    }
                    board.undoMove();

                    if (val.score > beta) {
                        ret_val = val;
                        prune = true;
                    } else if (val.score > alpha) {
                        alpha = val.score;
                        ret_val = val;
                        ret_val.move = moves[i];
                    }
                }
                if (ret_val === undefined) {
                    ret_val = { score: alpha };
                }
            }

            //ret_val = { move: best_move, score: best_score };
        }

        if (time_is_up) {
            ret_val = undefined;
        }
        return ret_val;

    }


/*
            function negamax(node, depth, α, β, color)
    if node is a terminal node or depth = 0
        return color * the heuristic value of node
    else
        foreach child of node
            val := -negamax(child, depth-1, -β, -α, -color)
            {the following if statement constitutes alpha-beta pruning}
            if val≥β
                return val
            if val≥α
                α:=val
        return α
*/
    function search(board, depth, startTime, maxTimeMS) {
        var score, board_score, moves, myMove, oppMove, i, j,
            best_move, best_score, ret_val, oppBestScore, prune, move;

        best_score = -99999;
        if (nodes_searched > nodeCheckThreshold) {
            if ((new Date()) - startTime > maxTimeMS) {
                time_is_up = true;
            } else {
                nodeCheckThreshold = nodes_searched + 10000;
            }
        }



        if (!time_is_up) {
            if (depth === 0) {
                ret_val = { score: calc_score(board) };
            } else {
                moves = board.movegen();

                for (i = 0; i < moves.myMoves.length && !time_is_up; i += 1) {
                    oppBestScore = 99999;
                    prune = false;
                    for (j = 0; j < moves.oppMoves.length && !prune && !time_is_up; j += 1) {
                        board.processMove(moves.myMoves[i], moves.oppMoves[j]);
                        move = search(board, depth - 1, startTime, maxTimeMS);
                        board.undoMove();
                        //Trace("Opp move  d:" + depth + " move:" + moves.oppMoves[j] + " score:" + board_score);

                        if (move !== undefined) {
                            board_score = move.score;
                            oppBestScore = Math.min(oppBestScore, board_score);

                            if (oppBestScore < best_score) {
                                prune = true;
                            }
                        }
                    }
                    if (oppBestScore > best_score) {
                        best_score = oppBestScore;
                        best_move = moves.myMoves[i];
                    }

                }

                ret_val = { move: best_move, score: best_score };
            }
        }
        if (time_is_up) {
            ret_val = undefined;
        }
        return ret_val;
    }

    function search_mgr(board, startDepth) {
        var currentDepth = startDepth, startTime = new Date(),
            move, bestMove, exitNow = false;

        nodes_searched = 0;
        nodeCheckThreshold = 10000;
        time_is_up = false;
        bestMove = {};
        move = negamax(board, 4, -99999, 99999, 1, startTime, 10000);
        //while (!exitNow) {
        //    trace("Searching " + currentDepth);
        //    move = negamax(board, currentDepth, -99999, 99999, MY, startTime, 1000);
        //    if (move !== undefined) {
        //        bestMove = move;
        //    } else {
        //        exitNow = true;
        //    }

        //    currentDepth += 1;
        //}

        return move;

    }

    function new_game() {
        num_cells = WIDTH * HEIGHT;
        num_item_types = get_number_of_item_types();
    }

    function make_move() {
        var board, min_dist, best_move, fruit_goal, i, move, start;

        halfFruit = [];
        for (i = 0; i < num_item_types; i += 1) {
            halfFruit[i] = get_total_item_count(i + 1) / 2;
        }


        Board.init(get_board());
        min_dist = 9e99;


        nodes_searched = 0;
        startTime = new Date();
        move = search_mgr(Board, 2);
        trace(nodes_searched * 1000 / ((new Date()) - startTime));

        return move.move;
    }


    return { new_game: new_game, make_move: make_move };

}());



function make_move() {
    "use strict";
    return ns.make_move();
}

function new_game() {
    "use strict";
    ns.new_game();
}
