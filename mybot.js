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
String.prototype.hashCode = function () {
    "use strict";
	var hash = 0;
	if (this.length == 0) return hash;
	for (i = 0; i < this.length; i++) {
		char = this.charCodeAt(i);
		hash = ((hash<<5)-hash)+char;
		hash = hash & hash; // Convert to 32bit integer
	}
	return hash;
}

var ns = (function () {
    "use strict";
    var MY = 0, OPP = 1, num_cells, num_types, x_delta, y_delta, pass, Board, num_item_types,
        max_depth = 4, nodes_searched, nodeCheckThreshold, time_is_up = false, halfFruit, startTime, move_idx,
        START = 0, COMPLETE = 1, SKIP = 2;


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
                    if (loc.x === loc_other.x && loc.y === loc_other.y) {
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

    function negamax(board, sd, depth, alpha, beta, side, startTime, maxTimeMS) {
        var ret_val, moves, i, j, val, best_move, best_score, prune, hash1, hash2, max;

        max = -9999;
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
                max = -9999;
                for (i = 0; i < moves.length && !time_is_up && !prune; i += 1) {
                    //hash1 = board.key();
                    board.processMove(moves[i]);
                    val = negamax(board, sd, depth - 1, -beta, -alpha, -side, startTime, maxTimeMS);
                    if (val !== undefined) {
                        val.score *= -1;
                        val.score -= 0.001 * (20 - depth);
                    } else {
                        break;
                    }
                    //if (depth === sd) {
                    //    trace("My move:" + moves[i] + " score: " + val.score);
                    //}
                    board.undoMove();
                    //hash2 = board.key();
                    //if(hash1 !== hash2) {
                    //    alert('Undo error');
                    //}

                    if (val.score > max) {
                        max = val.score;
                        ret_val = { score: max, move: moves[i] };
                    }
                    if (val.score > alpha) {
                        alpha = val.score;
                    }

                    if (alpha >= beta) {
                        ret_val.score = alpha;
                        prune = true;
                    }
                }
                if (ret_val === undefined) {
                    ret_val = { score: max };
                }
            }

            //ret_val = { move: best_move, score: best_score };
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
        //move = negamax(board, 4, -99999, 99999, 1, startTime, 10000);
        while (!exitNow) {
            trace("Searching " + currentDepth);
            move = negamax(board, currentDepth, currentDepth, -99999, 99999, 1, startTime, 9500);
            if (move !== undefined) {
                bestMove = move;
                trace("Best move: " + move.move);
            } else {
                exitNow = true;
            }

            currentDepth += 2;
        }

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
