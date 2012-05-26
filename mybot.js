var ns = new function() {

    var MY = 1, OPP = 2;
    var num_cells;
    var num_types;
    var x_delta = new Array();
    var y_delta = new Array();

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

    var std_moves = new Array( EAST, WEST, NORTH, SOUTH, TAKE, PASS );


    var pass = true;

    this.new_game = function() {
        num_cells = WIDTH * HEIGHT;
        num_types = get_number_of_item_types();
    }

    this.make_move = function() {
        var board = get_board();
        var min_dist = 9e99;
        var best_move;

        if( pass ) {
            pass = false;
            //return PASS;
        }

        //score(board);


        var fruit_goal=new Array();
        for(var i = 1; i <= get_number_of_item_types(); i++) {
            
            fruit_goal.push( { fruit:i, count:get_total_item_count(i) } );
        }
        fruit_goal.sort( function(a,b) { return b.count - a.count; } );

        board = reduce_board(board);


        return gravity(board);
    }


    function search() {
        var my_inv_moves = board.get_invalid_moves(MY);
        var opp_inv_moves = board.get_invalid_moves(OPP);

        var my_move,opp_move;

        for( my_move in std_moves ) {
            if( my_inv_moves.indexOf( my_move ) != -1 ) {
                continue;
            }
            for( opp_move in std_moves ) {
                if( opp_inv_moves.indexOf( opp_move ) != -1 ) {
                    continue;
                }

            }
        }
    }

    function reduce_board(board) {
        var new_board = new Array(WIDTH);
        for(var col = 0; col < WIDTH; col++) {
            new_board[col] = new Array(HEIGHT);
        }

        for(var row = 0; row < HEIGHT; row++) {
            for(var col = 0; col < WIDTH; col++) {
                new_board[col][row] = board[col][row];
                if(new_board[col][row] > 0) {
                    var t = new_board[col][row];
                    var total = get_total_item_count(t);
                    if( get_my_item_count(t) / total > 0.5 || get_opponent_item_count(t) / total > 0.5 ) {
                        new_board[col][row] = 0;
                    }
                }
            }
        }
        return new_board;
    }

    function gravity(board) {
        var mx = get_my_x();
        var my = get_my_y();
        var vector = { theta: 0, r: 0 };
        for(var row = 0; row < HEIGHT; row++) {
            for(var col = 0; col < WIDTH; col++) {
                if(board[col][row] > 0) {
                    var dx = col-mx;
                    var dy = row-my;
                    var dist = Math.sqrt(Math.pow(dx, 2) + Math.pow(dy,2));
                    if(dist==0) {
                        return TAKE;
                    }

                    var force = 1 / Math.pow(dist,2);
                    var theta = Math.atan2(-dy,dx);
                    var tx = vector.r * Math.cos(vector.theta);
                    var ty = vector.r * Math.sin(vector.theta);
                    tx += force * Math.cos(theta);
                    ty += force * Math.sin(theta);
                    vector.r = Math.sqrt(Math.pow(tx, 2) + Math.pow(ty,2));
                    vector.theta = Math.atan2(ty,tx);

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
        var d = vector.theta;
        if( d <= Math.PI / 4 && d > -Math.PI / 4 ) {
            return EAST;
        } else if( d >= Math.PI / 4 && d <  3 * Math.PI / 4 ) {
            return NORTH;
        } else if( d >= 3* Math.PI / 4 || d <= -3 * Math.PI / 4 ) {
            return WEST;
        } else {
            return SOUTH;
        }

    }


    function Board(init) {
        this.fruit_grid = new Array(num_cells);
        this.my_x = get_my_x();
        this.my_y = get_my_y();
        this.opp_x = get_opponent_x();
        this.opp_y = get_opponent_y();
    }

    Board.prototype.move = function(my_move, opp_move) {
        this.my_x += x_delta[my_move];
        this.my_y += y_delta[my_move];
        this.opp_x += x_delta[opp_move];
        this.opp_y += y_delta[opp_move];

        this.my_x = Math.max( this.my_x, 0 );
        this.my_x = Math.min( this.my_x, WIDTH-1 );
        this.my_y = Math.max( this.my_y, 0 );
        this.my_y = Math.min( this.my_y, WIDTH-1 );

        this.opp_x = Math.max( this.opp_x, 0 );
        this.opp_x = Math.min( this.opp_x, WIDTH-1 );
        this.opp_y = Math.max( this.opp_y, 0 );
        this.opp_y = Math.min( this.opp_y, WIDTH-1 );
    }

    Board.prototype.get_invalid_moves = function(side) {
        var x,y;
        var invalid_moves = new Array();

        if( side = MY )
            {
            x = this.my_x;
            y = this.my_y;
            }
        else
            {
            x = this.opp_x;
            y = this.opp_y;
            }

        if( x <= 0 ) {
            invalid_moves.push(WEST);
        } else if( x >= WIDTH-1 ) {
            invalid_moves.push(EAST);
        }

        if( y <= 0 ) {
            invalid_moves.push(NORTH);
        } else if( y >= HEIGHT-1 ) {
            invalid_moves.push(EAST);
        }

        return invalid_moves;
    }

    function xy2pos(x,y) {
        return y*WIDTH + x;
    }
};



function make_move() {
    return ns.make_move();
}

function new_game() {
    ns.new_game();
}
