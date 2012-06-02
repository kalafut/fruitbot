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
/**
 * JS Implementation of MurmurHash3 (r136) (as of May 20, 2011)
 *
 * @author <a href="mailto:gary.court@gmail.com">Gary Court</a>
 * @see http://github.com/garycourt/murmurhash-js
 * @author <a href="mailto:aappleby@gmail.com">Austin Appleby</a>
 * @see http://sites.google.com/site/murmurhash/
 *
 * @param {string} key ASCII only
 * @param {number} seed Positive integer only
 * @return {number} 32-bit positive integer hash
 */

var debug = 0;

function dbg_trace(s) {
    if (debug) {
        trace(s);
    }
}


function murmurhash3_32_gc(key, seed) {
	var remainder, bytes, h1, h1b, c1, c1b, c2, c2b, k1, i;

	remainder = key.length & 3; // key.length % 4
	bytes = key.length - remainder;
	h1 = seed;
	c1 = 0xcc9e2d51;
	c2 = 0x1b873593;
	i = 0;

	while (i < bytes) {
	  	k1 =
	  	  ((key.charCodeAt(i) & 0xff)) |
	  	  ((key.charCodeAt(++i) & 0xff) << 8) |
	  	  ((key.charCodeAt(++i) & 0xff) << 16) |
	  	  ((key.charCodeAt(++i) & 0xff) << 24);
		++i;

		k1 = ((((k1 & 0xffff) * c1) + ((((k1 >>> 16) * c1) & 0xffff) << 16))) & 0xffffffff;
		k1 = (k1 << 15) | (k1 >>> 17);
		k1 = ((((k1 & 0xffff) * c2) + ((((k1 >>> 16) * c2) & 0xffff) << 16))) & 0xffffffff;

		h1 ^= k1;
        h1 = (h1 << 13) | (h1 >>> 19);
		h1b = ((((h1 & 0xffff) * 5) + ((((h1 >>> 16) * 5) & 0xffff) << 16))) & 0xffffffff;
		h1 = (((h1b & 0xffff) + 0x6b64) + ((((h1b >>> 16) + 0xe654) & 0xffff) << 16));
	}

	k1 = 0;

	switch (remainder) {
		case 3: k1 ^= (key.charCodeAt(i + 2) & 0xff) << 16;
		case 2: k1 ^= (key.charCodeAt(i + 1) & 0xff) << 8;
		case 1: k1 ^= (key.charCodeAt(i) & 0xff);

		k1 = (((k1 & 0xffff) * c1) + ((((k1 >>> 16) * c1) & 0xffff) << 16)) & 0xffffffff;
		k1 = (k1 << 15) | (k1 >>> 17);
		k1 = (((k1 & 0xffff) * c2) + ((((k1 >>> 16) * c2) & 0xffff) << 16)) & 0xffffffff;
		h1 ^= k1;
	}

	h1 ^= key.length;

	h1 ^= h1 >>> 16;
	h1 = (((h1 & 0xffff) * 0x85ebca6b) + ((((h1 >>> 16) * 0x85ebca6b) & 0xffff) << 16)) & 0xffffffff;
	h1 ^= h1 >>> 13;
	h1 = ((((h1 & 0xffff) * 0xc2b2ae35) + ((((h1 >>> 16) * 0xc2b2ae35) & 0xffff) << 16))) & 0xffffffff;
	h1 ^= h1 >>> 16;

	return h1 >>> 0;
}

var testBoard1 = { board: [
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0] ],
    history: [
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0] ],
    numberOfItemTypes: 3,
    totalItems: [1, 3, 5],
    myBotCollected: [0.5, 1, 1,5],
    simpleBotCollected: [0.5, 1, 1,5],
    myX: 5,
    myY: 1,
    oppX: 5,
    oppY: 1,
    initial_state: {}
};

var ns = (function () {
    "use strict";
    var MY = 0, OPP = 1, num_cells, num_types, x_delta, y_delta, pass, Board, num_item_types,
        max_depth = 4, nodes_searched, nodeCheckThreshold, time_is_up = false, halfFruit, startTime, move_idx,
        START = 0, COMPLETE = 1, SKIP = 2, moveTrans, moveHist, evalCache, xlat;

    moveTrans = { NORTH: 'N', SOUTH: 'S', EAST: 'E', WEST: 'W', TAKE: 'T', PASS: 'P' };

    xlat = {
        EAST: "EAST",
        NORTH: "NORTH",
        WEST: "WEST",
        SOUTH: "SOUTH",
        TAKE: "TAKE",
        PASS: "PASS"
    };


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
        var score, material, i, types, row, col, dx, dy, dist, minDist, myLoc, oppLoc,
            myCats = 0, oppCats = 0, wonCats = [], cell, myCollected, oppCollected;


        nodes_searched += 1;

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
            return Infinity;
        } else if (oppCats > num_item_types / 2) {
            return -Infinity;
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
        var ret_val, moves, i, j, val, best_move, best_score, prune, hash1, hash2, max;
        var boardHash, cacheEval, moveList;

        if(depth === sd) {
            moveList = {};
        }

        max = -9999;
        if (nodes_searched > nodeCheckThreshold) {
            if ((new Date()) - startTime > maxTimeMS) {
                time_is_up = true;
            } else {
                nodeCheckThreshold = nodes_searched + 2000;
            }
        }

        if (!time_is_up) {
            if (depth === 0) {
                ret_val = { score: calc_score(board) };
            } else {
                prune = false;
                moves = board.movegen();
                //if(depth === sd && moveOrder !== undefined) {
                //    moves = moveOrder;
                //}

                max = -9999;
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
                    val = negamax(board, sd, depth - 1, -beta, -alpha, moveOrder, startTime, maxTimeMS);

                    if (val !== undefined) {
                        val.score *= -1;
                        val.score -= 0.001 * (20 - depth);
                    } else {
                        break;
                    }
                    if (depth === sd) {
                        moveList[moves[i]] = val.score;
                        dbg_trace("My move:" + moves[i] + " score: " + val.score);
                    }
                    board.undoMove();

                    if (depth === sd) {
                        moveList[moves[i]] = val.score;
                    }
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

                if (depth === sd) {
                    ret_val.moveList = moveList;
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
        var currentDepth = startDepth,
            move, moveList, bestMove, exitNow = false;

        nodes_searched = 0;
        nodeCheckThreshold = 10000;
        time_is_up = false;
        bestMove = {};

        //move = negamax(board, 4, -99999, 99999, 1, startTime, 10000);
        while (!exitNow) {
            dbg_trace("Searching " + currentDepth);
            move = negamax(board, currentDepth, currentDepth, -99999, 99999, moveList, startTime, 8000);
            if (move !== undefined) {
                bestMove = move;
                dbg_trace("Best move: " + move.move);
                //moveList = move.moveList
            } else {
                exitNow = true;
            }

            currentDepth += 1;
        }
        for(move in bestMove.moveList) {
            trace("Move: " + move.toString() + "  Score: " + bestMove.moveList[move]);
        }
        trace((currentDepth - 1).toString() + " ply / " + nodes_searched.toString() + " nodes / " +(((new Date()) - startTime)/1000).toString() + "s" );

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

        startTime = new Date();

        halfFruit = [];
        for (i = 0; i < num_item_types; i += 1) {
            halfFruit[i] = get_total_item_count(i + 1) / 2;
        }


        Board.init(get_board());
        min_dist = 9e99;


        nodes_searched = 0;
        move = search_mgr(Board, 4);
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

// Optionally include this function if you'd like to always reset to a
// certain board number/layout. This is useful for repeatedly testing your
// bot(s) against known positions.
//
function default_board_number() {
    //return 615808;
    //80777
    //764316
    //return 456645;
    //270909
    //return 62749;
    return 165134;
}

