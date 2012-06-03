var Board = {
    init: function(boardNumber) {
        var fullBoard, customSetup = false;

        if (typeof default_board_setup === 'function') {
            setup = default_board_setup();
            parsedSetup = Board.parseSetup(setup);
            if (parsedSetup) {
                WIDTH = parsedSetup.width;
                HEIGHT = parsedSetup.height;
                Board.numberOfItemTypes = parsedSetup.numberOfItemTypes;
                Board.totalItems = parsedSetup.totalItems;
                Board.myX = parsedSetup.myX;
                Board.myY = parsedSetup.myY;
                Board.oppX = parsedSetup.oppX;
                Board.oppY = parsedSetup.oppY;
                Board.myBotCollected = parsedSetup.myBotCollected;
                Board.simpleBotCollected = parsedSetup.simpleBotCollected;

                Board.board = [];
                for (var i=0; i<WIDTH; i++) {
                    Board.board[i] = [];
                    for (var j=0; j<HEIGHT; j++) {
                        Board.board[i][j] = parsedSetup.board[j][i];
                    }
                }
                Board.history = new Array(WIDTH);

                for (var i=0; i<WIDTH; i++) {
                    Board.history[i] = new Array(HEIGHT);
                    for (var j=0; j<HEIGHT; j++) {
                        Board.history[i][j] = 0;
                    }
                }
            customSetup = true;
            }
        }
        if(!customSetup) {
            Board.initRandom(boardNumber);

        Board.initRandom(boardNumber);

            // initialize board
            HEIGHT = Math.min(Math.floor(Board.random() * 11) + 5, 15);
            WIDTH = Math.min(Math.floor(Board.random() * 11) + 5, 15);

            Board.board = new Array(WIDTH);

            for (var i=0; i<WIDTH; i++) {
                Board.board[i] = new Array(HEIGHT);
                for (var j=0; j<HEIGHT; j++) {
                    Board.board[i][j] = 0;
                }
            }

            Board.history = new Array(WIDTH);

            for (var i=0; i<WIDTH; i++) {
                Board.history[i] = new Array(HEIGHT);
                for (var j=0; j<HEIGHT; j++) {
                    Board.history[i][j] = 0;
                }
            }

            // initialize items on board
            do {
                Board.numberOfItemTypes = Math.floor(Board.random() * 3 + 3);
            } while(Board.numberOfItemTypes * Board.numberOfItemTypes >= HEIGHT * WIDTH)
            Board.totalItems = new Array();
            Board.simpleBotCollected = new Array(Board.numberOfItemTypes);
            Board.myBotCollected = new Array(Board.numberOfItemTypes);
            var x;
            var y;
            for (var i=0; i<Board.numberOfItemTypes; i++) {
                Board.myBotCollected[i] = 0;
                Board.simpleBotCollected[i] = 0;
                Board.totalItems[i] = i * 2 + 1;
                for (var j=0; j<Board.totalItems[i]; j++) {
                    do {
                        x = Math.min(Math.floor(Board.random() * WIDTH), WIDTH);
                        y = Math.min(Math.floor(Board.random() * HEIGHT), HEIGHT);
                    } while (Board.board[x][y] != 0);
                    Board.board[x][y] = i + 1;
                }
            }

            // get them the same starting position
            do {
                x = Math.min(Math.floor(Board.random() * WIDTH), WIDTH);
                y = Math.min(Math.floor(Board.random() * HEIGHT), HEIGHT);
            } while (Board.board[x][y] != 0);
            Board.myX = x;
            Board.myY = y;
            Board.oppX = x;
            Board.oppY = y;
        }
        Board.initial_state = {};
        jQuery.extend(true, Board.initial_state, Board);
    },
    reset: function() {
        Board = Board.initial_state;
        Board.initial_state = {};
        jQuery.extend(true, Board.initial_state, Board);
        Board.newGame();
        GamePlay.start();
    },
    newGame: function() {
        var new_game_exists = undefined;
        try {
            new_game_exists = new_game;
        } catch(e) {
        }
        if(new_game_exists !== undefined) {
            new_game();
        }
        // SimpleBot currently doesn't need any sort of init, but if it did, it'd be called here too
    },
    processMove: function() {
        var myMove = make_move();
        var simpleBotMove = SimpleBot.makeMove();
        if ((Board.myX == Board.oppX) && (Board.myY == Board.oppY) && (myMove == TAKE) && (simpleBotMove == TAKE) && Board.board[Board.myX][Board.myY] > 0) {
            Board.myBotCollected[Board.board[Board.myX][Board.myY]-1] = Board.myBotCollected[Board.board[Board.myX][Board.myY]-1] + 0.5;
            Board.simpleBotCollected[Board.board[Board.oppX][Board.oppY]-1] = Board.simpleBotCollected[Board.board[Board.oppX][Board.oppY]-1] + 0.5;
            Board.board[Board.myX][Board.myY] = 0; 
        } else {
            if (myMove == TAKE && Board.board[Board.myX][Board.myY] > 0) {
                Board.myBotCollected[Board.board[Board.myX][Board.myY]-1]++;
                Board.board[Board.myX][Board.myY] = 0; 
            }
            if (simpleBotMove == TAKE && Board.board[Board.oppX][Board.oppY] > 0) {
                Board.simpleBotCollected[Board.board[Board.oppX][Board.oppY]-1]++;
                Board.board[Board.oppX][Board.oppY] = 0; 
            }
        }
        if (myMove == NORTH) {
            if (Board.myY - 1 >= 0) {
                Board.myY = Board.myY - 1;
            }
        }
        if (simpleBotMove == NORTH) {
            if (Board.oppY - 1 >= 0) {
                Board.oppY = Board.oppY - 1;
            }
        }
        if (myMove == SOUTH) {
            if (Board.myY + 1 < HEIGHT) {
                Board.myY = Board.myY + 1;
            }
        }
        if (simpleBotMove == SOUTH) {
            if (Board.oppY + 1 < HEIGHT) {
                Board.oppY = Board.oppY + 1;
            }
        }
        if (myMove == EAST) {
            if (Board.myX + 1 < WIDTH) {
                Board.myX = Board.myX + 1;
            }
        }
        if (simpleBotMove == EAST) {
            if (Board.oppX + 1 < WIDTH) {
                Board.oppX = Board.oppX + 1;
            }
        }
        if (myMove == WEST) {
            if (Board.myX - 1 >= 0) {
                Board.myX = Board.myX - 1;
            }
        }
        if (simpleBotMove == WEST) {
            if (Board.oppX - 1 >= 0) {
                Board.oppX = Board.oppX - 1;
            }
        }

        Board.history[Board.myX][Board.myY] |= 1;
        Board.history[Board.oppX][Board.oppY] |= 2;

    },
    noMoreItems: function() {
        for (var i=0; i<WIDTH; i++) {
            for (var j=0; j<HEIGHT; j++) {
                if (Board.board[i][j] != 0) {
                    return false;
                }
            }
        }
        return true;
    },
    initRandom: function(boardNumber) {
        // Create a random number generator (PRNG) for board
        // setup use and one for any other use. Doing this
        // allows us to better control the sequence of numbers
        // we receive. Only those functions generating random
        // numbers for board setup should call Board.random().

        Math.seedrandom(boardNumber);
        Board.boardSetupPRNG = Math.random;
        Math.seedrandom();
        Board.normalPRNG = Math.random;
    },
    random: function() {
        // Generate a random number from the board setup 
        // PRNG and then switch Math.random back to the normal PRNG.
        var number;

        Math.random = Board.boardSetupPRNG;
        number = Math.random();
        Math.random = Board.normalPRNG;

        return number;
    },
    parseSetup: function(setup) {
        var parsedSetup = {},
            fruit = { 'A':1, 'B':2, 'C':3, 'M':4, 'O':5 },
            totalItems = [],
            board = [],
            i, j, f;

        parsedSetup.numberOfItemTypes = 0;
        try {
            // Check dimensions
            if ( (setup.width >= 5 && setup.width <= 15) && (setup.height >= 5 && setup.height <=15) ) {
                parsedSetup.width = setup.width;
                parsedSetup.height = setup.height;
            } else {
                return undefined;
            }

            // Check fruit
            if (setup.myFruit.length == 5 && setup.oppFruit.length == 5) {
                for (i = 0; i < 5; i++) {
                    if (setup.myFruit[i] >= 0 && setup.myFruit[i] <= 9 && setup.oppFruit[i] >= 0 && setup.oppFruit[i] <= 9 ) {
                        parsedSetup.myBotCollected = setup.myFruit;
                        parsedSetup.simpleBotCollected = setup.oppFruit;
                        if(setup.myFruit[i] > 0 || setup.oppFruit[i] > 0) {
                            parsedSetup.numberOfItemTypes += 1;
                            totalItems[i] = (totalItems[i] | 0) + setup.myFruit[i] + setup.oppFruit[i];
                        }
                    } else {
                        return undefined;
                    }
                }
            } else {
                return undefined;
            }

            // parse board
            if( setup.board.length !== 15*2 + 1 ) {
                return undefined;
            }

            for (i = 1; i < setup.board.length; i += 2) {
                cells = setup.board[i].split('|');
                row = [];
                for (j = 1; j < cells.length - 1; j++) {
                    cell = cells[j];
                    if (cell.indexOf('@') !== -1) {
                        parsedSetup.myX = j - 1;
                        parsedSetup.myY = (i - 1)/2;
                    }
                    if (cell.indexOf('%') !== -1) {
                        parsedSetup.oppX = j - 1;
                        parsedSetup.oppY = (i - 1)/2;
                    }
                    for (f in fruit) {
                        if (cell.indexOf(f) !== -1) {
                            row[j-1] = fruit[f];
                            parsedSetup.numberOfItemTypes = Math.max(parsedSetup.numberOfItemTypes, fruit[f]);
                            totalItems[fruit[f]-1] = (totalItems[fruit[f]-1] | 0) + 1;
                            break;
                        }
                    }
                    if (row[j-1] === undefined) {
                        row[j-1] = 0;
                    }
                }
                board.push(row);
            }
        } catch (e) {
            return undefined
        }
        parsedSetup.totalItems = totalItems;
        parsedSetup.board = board;
        return parsedSetup;
    }

}

// Everything below is are API commands you can use.
// This, however, is not the actual API that's on the server
// but rather a working model of it for the purposes of giving
// you an environment to develop and debug in.

// don't rely on these constants to be the exact value listed here
var EAST = "EAST";
var NORTH = "NORTH";
var WEST = "WEST";
var SOUTH = "SOUTH";
var TAKE = "TAKE";
var PASS = "PASS";

var HEIGHT;
var WIDTH;

function has_item(i) {
    return i > 0;
}

function get_board() {
    return Board.board;
}

function get_number_of_item_types() {
    return Board.numberOfItemTypes;
}

function get_my_x() {
    return Board.myX;
}

function get_my_y() {
    return Board.myY;
}

function get_opponent_x() {
    return Board.oppX;
}

function get_opponent_y() {
    return Board.oppY;
}

function get_my_item_count(type) {
    return Board.myBotCollected[type-1];
}

function get_opponent_item_count(type) {
    return Board.simpleBotCollected[type-1];
}

function get_total_item_count(type) {
    return Board.totalItems[type-1];
}

function trace(mesg) {
    console.log(mesg);
}


