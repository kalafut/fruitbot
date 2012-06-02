/*global WIDTH, HEIGHT, get_number_of_item_types, get_my_x, get_my_y, get_opponent_x, get_opponent_y, EAST, NORTH, WEST, SOUTH, TAKE, PASS */
/*global get_board, get_total_item_count, get_my_item_count, get_opponent_item_count, trace */

var ns = (function () {
    "use strict";
    var MY, OPP, num_cells, num_types, x_delta, y_delta, pass, Board, num_item_types,
        max_depth = 4, nodes_searched, nodeCheckThreshold, time_is_up = false, halfFruit, startTime;


    Board = {
        init: function (start_board) {
            var i, j, x, y;

            // initialize board
            Board.board = [];
            Board.move_num = 0;

            for (i = 0; i < WIDTH; i += 1) {
                Board.board[i] = [];
                for (j = 0; j < HEIGHT; j += 1) {
                    Board.board[i][j] = start_board[i][j];
                }
            }

            Board.history = [];

            Board.oppCollected = [];
            Board.myCollected = [];
            for (i = 0; i < get_number_of_item_types(); i += 1) {
                Board.myCollected[i] = get_my_item_count(i + 1);
                Board.oppCollected[i] = get_opponent_item_count(i + 1);
            }

            Board.myX = get_my_x();
            Board.myY = get_my_y();
            Board.oppX = get_opponent_x();
            Board.oppY = get_opponent_y();
        },
        processMove: function (myMove, oppMove) {
            var undo = {
                myX: Board.myX,
                myY: Board.myY,
                oppX: Board.oppX,
                oppY: Board.oppY
            };
            Board.history.push(undo);
            Board.move_num += 1;

            if ((Board.myX === Board.oppX) && (Board.myY === Board.oppY) && (myMove === TAKE) && (oppMove === TAKE) && Board.board[Board.myX][Board.myY] > 0) {
                undo.myFruitType = Board.board[Board.myX][Board.myY];
                undo.myFruitX = Board.myX;
                undo.myFruitY = Board.myY;
                undo.myFruitCnt = 0.5;

                undo.oppFruitType = Board.board[Board.oppX][Board.oppY];
                undo.oppFruitX = Board.oppX;
                undo.oppFruitY = Board.oppY;
                undo.oppFruitCnt = 0.5;

                Board.myCollected[Board.board[Board.myX][Board.myY] - 1] = Board.myCollected[Board.board[Board.myX][Board.myY] - 1] + 0.5;
                Board.oppCollected[Board.board[Board.oppX][Board.oppY] - 1] = Board.oppCollected[Board.board[Board.oppX][Board.oppY] - 1] + 0.5;
                Board.board[Board.myX][Board.myY] = 0;

            } else {
                if (myMove === TAKE && Board.board[Board.myX][Board.myY] > 0) {
                    undo.myFruitType = Board.board[Board.myX][Board.myY];
                    undo.myFruitX = Board.myX;
                    undo.myFruitY = Board.myY;
                    undo.myFruitCnt = 1;

                    Board.myCollected[Board.board[Board.myX][Board.myY] - 1] += 1;
                    Board.board[Board.myX][Board.myY] = 0;
                }
                if (oppMove === TAKE && Board.board[Board.oppX][Board.oppY] > 0) {
                    undo.oppFruitType = Board.board[Board.oppX][Board.oppY];
                    undo.oppFruitX = Board.oppX;
                    undo.oppFruitY = Board.oppY;
                    undo.oppFruitCnt = 1;

                    Board.oppCollected[Board.board[Board.oppX][Board.oppY] - 1] += 1;
                    Board.board[Board.oppX][Board.oppY] = 0;
                }
            }
            if (myMove === NORTH) {
                if (Board.myY - 1 >= 0) {
                    Board.myY = Board.myY - 1;
                }
            }
            if (oppMove === NORTH) {
                if (Board.oppY - 1 >= 0) {
                    Board.oppY = Board.oppY - 1;
                }
            }
            if (myMove === SOUTH) {
                if (Board.myY + 1 < HEIGHT) {
                    Board.myY = Board.myY + 1;
                }
            }
            if (oppMove === SOUTH) {
                if (Board.oppY + 1 < HEIGHT) {
                    Board.oppY = Board.oppY + 1;
                }
            }
            if (myMove === EAST) {
                if (Board.myX + 1 < WIDTH) {
                    Board.myX = Board.myX + 1;
                }
            }
            if (oppMove === EAST) {
                if (Board.oppX + 1 < WIDTH) {
                    Board.oppX = Board.oppX + 1;
                }
            }
            if (myMove === WEST) {
                if (Board.myX - 1 >= 0) {
                    Board.myX = Board.myX - 1;
                }
            }
            if (oppMove === WEST) {
                if (Board.oppX - 1 >= 0) {
                    Board.oppX = Board.oppX - 1;
                }
            }

        },
        undoMove: function () {
            var undo = Board.history.pop();

            Board.move_num -= 1;

            Board.myX = undo.myX;
            Board.myY = undo.myY;
            if (undo.myFruitType !== undefined) {
                Board.myCollected[undo.myFruitType - 1] -= undo.myFruitCnt;
                Board.board[undo.myX][undo.myY] = undo.myFruitType;
            }

            Board.oppX = undo.oppX;
            Board.oppY = undo.oppY;
            if (undo.oppFruitType !== undefined) {
                Board.oppCollected[undo.oppFruitType - 1] -= undo.oppFruitCnt;
                Board.board[undo.oppX][undo.oppY] = undo.oppFruitType;
            }
        },

        noMoreItems: function () {
            var i, j;
            for (i = 0; i < WIDTH; i += 1) {
                for (j = 0; j < HEIGHT; j += 1) {
                    if (Board.board[i][j] !== 0) {
                        return false;
                    }
                }
            }
            return true;
        },
        movegen: function () {
            var moves, gen;

            gen = function (x, y) {
                //var moves = [PASS]; // PASS is probably a waste of search time
                var moves = []; // PASS is probably a waste of search time
                if (Board.board[x][y] > 0) {
                    moves.push(TAKE);
                }
                if (x >= 1) {
                    moves.push(WEST);
                }
                if (x <= WIDTH - 2) {
                    moves.push(EAST);
                }
                if (y >= 1) {
                    moves.push(NORTH);
                }
                if (y <= HEIGHT - 2) {
                    moves.push(SOUTH);
                }
                return moves;
            };

            moves = {
                myMoves: gen(Board.myX, Board.myY),
                oppMoves: gen(Board.oppX, Board.oppY)
            };

            return moves;
        }
    };

    MY = 1;
    OPP = 2;
    x_delta = [];
    y_delta = [];

    x_delta[EAST] = 1;
    x_delta[WEST] = -1;
    x_delta[NORTH] = 0;
    x_delta[SOUTH] = 0;
    x_delta[TAKE] = 0;
    x_delta[PASS] = 0;

    y_delta[EAST] = 0;
    y_delta[WEST] = 0;
    y_delta[NORTH] = -1;
    y_delta[SOUTH] = 1;
    y_delta[TAKE] = 0;
    y_delta[PASS] = 0;


    pass = true;

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
        var score, material, i, types, row, col, dx, dy, dist, min_dist,
            myCats = 0, oppCats = 0, wonCats = [], cell;

        nodes_searched += 1;

        // First award categories won
        for (i = 0; i < num_item_types; i += 1) {
            if (board.myCollected[i] > halfFruit[i]) {
                myCats += 1;
                wonCats.push(i);
            } else if (board.oppCollected[i] > halfFruit[i]) {
                oppCats += 1;
                wonCats.push(i);
            }
        }

        min_dist = 9999;
        for (row = 0; row < HEIGHT; row += 1) {
            for (col = 0; col < WIDTH; col += 1) {
                cell = board.board[col][row];
                if (cell > 0 && wonCats.indexOf(cell - 1) === -1) {
                    dx = col - board.myX;
                    dy = row - board.myY;
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
                material += board.myCollected[i] - board.oppCollected[i];
            }
        }

        score = 5 * (myCats - oppCats) + material - 0.01 * min_dist;

        return score;
    }


    function search(board, depth, startTime, maxTimeMS) {
        var score, board_score, moves, myMove, oppMove, i, j,
            best_moves=[], best_score, ret_val, oppBestScore, prune, move;

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
                        //trace("Opp move  d:" + depth + " move:" + moves.oppMoves[j] + " score:" + board_score);

                        if (move !== undefined) {
                            board_score = move.score;
                            oppBestScore = Math.min(oppBestScore, board_score);

                            if (oppBestScore < best_score) {
                                prune = true;
                            }
                        }
                    }
                    //if (depth === max_depth) {
                    //    //trace("My move:" + moves.myMoves[i] + " score: " + oppBestScore);
                    //}
                    if (oppBestScore > best_score) {
                        best_score = oppBestScore;
                        best_moves = [moves.myMoves[i]];
                    } else if (oppBestScore == best_score) {
                        best_moves.push(moves.myMoves[i]);
                    }
                }

                ret_val = { moves: best_moves, score: best_score };
            }
        }
        if (time_is_up) {
            ret_val = undefined;
        }
        return ret_val;
    }

    function search_mgr(board, startDepth) {
        var currentDepth = startDepth, startTime = new Date(),
            moves, bestMoves, exitNow = false, lastDepth, earlyBestMoves, lateBestMoves, bestMove, i;

        nodes_searched = 0;
        nodeCheckThreshold = 10000;
        time_is_up = false
        bestMoves = [];
        while (!exitNow) {
            trace("Searching " + currentDepth);
            moves = search(board, currentDepth, startTime, 9500);
            if (moves !== undefined) {
                bestMoves[currentDepth] = moves;
            } else {
                exitNow = true;
            }

            currentDepth += 1;
        }

        lastDepth = currentDepth - 2;
        earlyBestMoves = bestMoves[startDepth].moves;
        lateBestMoves = bestMoves[lastDepth].moves;
            
        for(i = 0; i < lateBestMoves.length && bestMove === undefined; i++) {
            if (earlyBestMoves.indexOf(lateBestMoves[i]) !== -1) {
                bestMove = lateBestMoves[i];
            }
        }
        if (bestMove === undefined) {
            bestMove = lateBestMoves[0];
        }

        return { move: bestMove };
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

        if (pass) {
            pass = false;
            //return PASS;
        }

        //score(board);
        fruit_goal = [];
        for (i = 1; i <= get_number_of_item_types(); i += 1) {
            fruit_goal.push({
                fruit: i,
                count: get_total_item_count(i)
            });
        }
        fruit_goal.sort(function (a, b) {
            return b.count - a.count;
        });

        //board = reduce_board(board);

        nodes_searched = 0;
        startTime = new Date();
        move = search_mgr(Board, 1);
        //trace(nodes_searched * 1000 / ((new Date()) - startTime));

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

