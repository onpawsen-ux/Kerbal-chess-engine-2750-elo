#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>
#include <chrono>
#include <cctype>
#include <cstring>
#include <random>

// Piece representations
enum { EMPTY, WP, WN, WB, WR, WQ, WK, BP, BN, BB, BR, BQ, BK };
enum { WHITE, BLACK, BOTH };
enum { TT_EXACT, TT_ALPHA, TT_BETA };

// Structures for moves and board state
struct Move {
    int from;
    int to;
    int promoted; // 0 if none, otherwise the piece code
    int score;    // Move ordering score

    bool operator==(const Move& other) const {
        return from == other.from && to == other.to && promoted == other.promoted;
    }
};

struct MoveList {
    Move moves[256];
    int count = 0;
    void push(const Move& m) {
        if (count < 256) {
            moves[count++] = m;
        }
    }
};

struct BoardState {
    int board[128]; // 0x88 board
    int side;       // Active player (WHITE or BLACK)
    int castling;   // Castling rights bitmask: 1=WK, 2=WQ, 4=BK, 8=BQ
    int enpassant;  // Square index or -1
    uint64_t hash;  // Zobrist Hash Key
};

// Transposition Table Entry
struct TTEntry {
    uint64_t key;
    int depth;
    int flag;
    int value;
    Move best_move;
};

// Global variables for search limits
std::chrono::time_point<std::chrono::steady_clock> search_start;
double search_time_limit_ms = 1000.0;
bool search_stopped = false;
int nodes_searched = 0;

// Zobrist keys
uint64_t piece_keys[13][128];
uint64_t side_key;
uint64_t castle_keys[16];
uint64_t ep_keys[128];

// Transposition Table
const int TT_SIZE = 1 << 20; // 1M entries, ~24MB memory
TTEntry* transposition_table = nullptr;

// Killer Moves for move ordering
Move killer_moves[2][64]; // [primary/secondary][ply]

// Piece values for material evaluation
const int piece_values[] = { 0, 100, 320, 330, 500, 900, 20000, 100, 320, 330, 500, 900, 20000 };

// Piece-Square Tables (PST) from white's perspective
const int pawn_table[64] = {
    0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
     5,  5, 10, 25, 25, 10,  5,  5,
     0,  0,  0, 20, 20,  0,  0,  0,
     5, -5,-10,  0,  0,-10, -5,  5,
     5, 10, 10,-20,-20, 10, 10,  5,
     0,  0,  0,  0,  0,  0,  0,  0
};

const int knight_table[64] = {
    -50,-40,-30,-30,-30,-30,-40,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 10, 15, 15, 10,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 10, 15, 15, 10,  5,-30,
    -40,-20,  0,  5,  5,  0,-20,-40,
    -50,-40,-30,-30,-30,-30,-40,-50
};

const int bishop_table[64] = {
    -20,-10,-10,-10,-10,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5, 10, 10,  5,  0,-10,
    -10,  5,  5, 10, 10,  5,  5,-10,
    -10,  0, 10, 10, 10, 10,  0,-10,
    -10, 10, 10, 10, 10, 10, 10,-10,
    -10,  5,  0,  0,  0,  0,  5,-10,
    -20,-10,-10,-10,-10,-10,-10,-20
};

const int rook_table[64] = {
      0,  0,  0,  0,  0,  0,  0,  0,
      5, 10, 10, 10, 10, 10, 10,  5,
     -5,  0,  0,  0,  0,  0,  0, -5,
     -5,  0,  0,  0,  0,  0,  0, -5,
     -5,  0,  0,  0,  0,  0,  0, -5,
     -5,  0,  0,  0,  0,  0,  0, -5,
     -5,  0,  0,  0,  0,  0,  0, -5,
      0,  0,  0,  5,  5,  0,  0,  0
};

const int queen_table[64] = {
    -20,-10,-10, -5, -5,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5,  5,  5,  5,  0,-10,
     -5,  0,  5,  5,  5,  5,  0, -5,
      0,  0,  5,  5,  5,  5,  0, -5,
    -10,  5,  5,  5,  5,  5,  0,-10,
    -10,  0,  5,  0,  0,  0,  0,-10,
    -20,-10,-10, -5, -5,-10,-10,-20
};

const int king_middle_table[64] = {
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -20,-30,-30,-40,-40,-30,-30,-20,
    -10,-20,-20,-20,-20,-20,-20,-10,
     20, 20,  0,  0,  0,  0, 20, 20,
     20, 30, 10,  0,  0, 10, 30, 20
};

const int king_end_table[64] = {
    -50,-40,-30,-20,-20,-30,-40,-50,
    -30,-20,-10,  0,  0,-10,-20,-30,
    -30,-10, 20, 30, 30, 20,-10,-30,
    -30,-10, 30, 40, 40, 30,-10,-30,
    -30,-10, 30, 40, 40, 30,-10,-30,
    -30,-10, 20, 30, 30, 20,-10,-30,
    -30,-30,  0,  0,  0,  0,-30,-30,
    -50,-30,-30,-30,-30,-30,-30,-50
};

// Helper utilities
inline int get_color(int piece) {
    if (piece == EMPTY) return BOTH;
    return (piece <= WK) ? WHITE : BLACK;
}

inline int square_to_64(int sq) {
    return (sq >> 4) * 8 + (sq & 7);
}

std::string square_to_uci(int sq) {
    if (sq & 0x88) return "";
    int rank = sq >> 4;
    int file = sq & 7;
    char f = 'a' + file;
    char r = '1' + rank;
    std::string s = "";
    s += f;
    s += r;
    return s;
}

int uci_to_square(const std::string& uci) {
    if (uci.length() < 2) return -1;
    int file = uci[0] - 'a';
    int rank = uci[1] - '1';
    if (file < 0 || file > 7 || rank < 0 || rank > 7) return -1;
    return (rank << 4) + file;
}

char piece_to_promotion_char(int piece) {
    switch (piece) {
        case WN: case BN: return 'n';
        case WB: case BB: return 'b';
        case WR: case BR: return 'r';
        case WQ: case BQ: return 'q';
        default: return ' ';
    }
}

// Initialize Zobrist hashing random keys
void init_zobrist() {
    std::mt19937_64 gen(10398012); // Seeded for reproducibility
    std::uniform_int_distribution<uint64_t> dis;
    for (int p = 0; p < 13; ++p) {
        for (int sq = 0; sq < 128; ++sq) {
            piece_keys[p][sq] = dis(gen);
        }
    }
    side_key = dis(gen);
    for (int i = 0; i < 16; ++i) {
        castle_keys[i] = dis(gen);
    }
    for (int i = 0; i < 128; ++i) {
        ep_keys[i] = dis(gen);
    }
}

// Generate the initial hash for a position
uint64_t generate_hash(const BoardState& state) {
    uint64_t h = 0;
    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece != EMPTY) {
            h ^= piece_keys[piece][sq];
        }
    }
    if (state.side == BLACK) h ^= side_key;
    h ^= castle_keys[state.castling];
    if (state.enpassant != -1) {
        h ^= ep_keys[state.enpassant];
    }
    return h;
}

// Setup Transposition Table
void init_tt() {
    if (transposition_table) delete[] transposition_table;
    transposition_table = new TTEntry[TT_SIZE]();
}

void clear_tt() {
    if (transposition_table) {
        std::memset(transposition_table, 0, sizeof(TTEntry) * TT_SIZE);
    }
}

// Convert mate scores to be relative to root
inline int score_to_tt(int score, int ply) {
    if (score > 25000) return score + ply;
    if (score < -25000) return score - ply;
    return score;
}

inline int score_from_tt(int score, int ply) {
    if (score > 25000) return score - ply;
    if (score < -25000) return score + ply;
    return score;
}

// Probe the TT
bool tt_probe(uint64_t key, int depth, int ply, int alpha, int beta, int& score, Move& best_move) {
    TTEntry& entry = transposition_table[key % TT_SIZE];
    if (entry.key == key) {
        best_move = entry.best_move;
        if (entry.depth >= depth) {
            int tt_val = score_from_tt(entry.value, ply);
            if (entry.flag == TT_EXACT) {
                score = tt_val;
                return true;
            }
            if (entry.flag == TT_ALPHA && tt_val <= alpha) {
                score = alpha;
                return true;
            }
            if (entry.flag == TT_BETA && tt_val >= beta) {
                score = beta;
                return true;
            }
        }
    }
    return false;
}

// Store in the TT
void tt_store(uint64_t key, int depth, int ply, int flag, int score, const Move& best_move) {
    TTEntry& entry = transposition_table[key % TT_SIZE];
    if (entry.key == 0 || entry.depth <= depth) {
        entry.key = key;
        entry.depth = depth;
        entry.flag = flag;
        entry.value = score_to_tt(score, ply);
        entry.best_move = best_move;
    }
}

// Store a killer move for ordering
void store_killer(const Move& m, int ply) {
    if (ply < 64) {
        if (!(killer_moves[0][ply] == m)) {
            killer_moves[1][ply] = killer_moves[0][ply];
            killer_moves[0][ply] = m;
        }
    }
}

// Check if a square is attacked by a specific color
bool is_square_attacked(const BoardState& state, int sq, int attacker_side) {
    int opp_color = attacker_side;

    // Knight attacks
    int knight_offsets[] = {-33, -31, -18, -14, 14, 18, 31, 33};
    for (int offset : knight_offsets) {
        int target = sq + offset;
        if (!(target & 0x88)) {
            int piece = state.board[target];
            if (piece != EMPTY && get_color(piece) == opp_color) {
                if (piece == WN || piece == BN) return true;
            }
        }
    }

    // Bishop / Queen sliding attacks
    int bishop_offsets[] = {-17, -15, 15, 17};
    for (int offset : bishop_offsets) {
        int target = sq + offset;
        while (!(target & 0x88)) {
            int piece = state.board[target];
            if (piece != EMPTY) {
                if (get_color(piece) == opp_color) {
                    if (piece == WB || piece == BB || piece == WQ || piece == BQ) return true;
                }
                break;
            }
            target += offset;
        }
    }

    // Rook / Queen sliding attacks
    int rook_offsets[] = {-16, -1, 1, 16};
    for (int offset : rook_offsets) {
        int target = sq + offset;
        while (!(target & 0x88)) {
            int piece = state.board[target];
            if (piece != EMPTY) {
                if (get_color(piece) == opp_color) {
                    if (piece == WR || piece == BR || piece == WQ || piece == BQ) return true;
                }
                break;
            }
            target += offset;
        }
    }

    // Pawn attacks
    if (opp_color == WHITE) {
        int targets[] = {sq - 17, sq - 15};
        for (int t : targets) {
            if (!(t & 0x88)) {
                if (state.board[t] == WP) return true;
            }
        }
    } else {
        int targets[] = {sq + 17, sq + 15};
        for (int t : targets) {
            if (!(t & 0x88)) {
                if (state.board[t] == BP) return true;
            }
        }
    }

    // King attacks
    int king_offsets[] = {-17, -16, -15, -1, 1, 15, 16, 17};
    for (int offset : king_offsets) {
        int target = sq + offset;
        if (!(target & 0x88)) {
            int piece = state.board[target];
            if (piece != EMPTY && get_color(piece) == opp_color) {
                if (piece == WK || piece == BK) return true;
            }
        }
    }

    return false;
}

// Checks if the active side is in check
bool is_in_check(const BoardState& state) {
    int us = state.side;
    int them = (us == WHITE) ? BLACK : WHITE;
    int king_sq = -1;
    int target_king = (us == WHITE) ? WK : BK;
    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        if (state.board[sq] == target_king) {
            king_sq = sq;
            break;
        }
    }
    if (king_sq == -1) return false;
    return is_square_attacked(state, king_sq, them);
}

// Used to prevent Zugzwang in Null Move Pruning
bool has_non_pawn_material(const BoardState& state, int side) {
    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece != EMPTY && get_color(piece) == side) {
            if (piece != WP && piece != BP && piece != WK && piece != BK) {
                return true;
            }
        }
    }
    return false;
}

// Move generation
void generate_moves(const BoardState& state, MoveList& list) {
    int us = state.side;
    int them = (us == WHITE) ? BLACK : WHITE;

    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece == EMPTY || get_color(piece) != us) continue;

        // White Pawn moves
        if (piece == WP) {
            int to = sq + 16;
            if (!(to & 0x88) && state.board[to] == EMPTY) {
                if ((to >> 4) == 7) {
                    list.push({sq, to, WQ, 0});
                    list.push({sq, to, WR, 0});
                    list.push({sq, to, WB, 0});
                    list.push({sq, to, WN, 0});
                } else {
                    list.push({sq, to, 0, 0});
                    int to2 = sq + 32;
                    if ((sq >> 4) == 1 && state.board[to2] == EMPTY) {
                        list.push({sq, to2, 0, 0});
                    }
                }
            }
            int caps[] = {sq + 15, sq + 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (state.board[to_cap] != EMPTY && get_color(state.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 7) {
                            list.push({sq, to_cap, WQ, 0});
                            list.push({sq, to_cap, WR, 0});
                            list.push({sq, to_cap, WB, 0});
                            list.push({sq, to_cap, WN, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == state.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        }
        // Black Pawn moves
        else if (piece == BP) {
            int to = sq - 16;
            if (!(to & 0x88) && state.board[to] == EMPTY) {
                if ((to >> 4) == 0) {
                    list.push({sq, to, BQ, 0});
                    list.push({sq, to, BR, 0});
                    list.push({sq, to, BB, 0});
                    list.push({sq, to, BN, 0});
                } else {
                    list.push({sq, to, 0, 0});
                    int to2 = sq - 32;
                    if ((sq >> 4) == 6 && state.board[to2] == EMPTY) {
                        list.push({sq, to2, 0, 0});
                    }
                }
            }
            int caps[] = {sq - 15, sq - 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (state.board[to_cap] != EMPTY && get_color(state.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 0) {
                            list.push({sq, to_cap, BQ, 0});
                            list.push({sq, to_cap, BR, 0});
                            list.push({sq, to_cap, BB, 0});
                            list.push({sq, to_cap, BN, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == state.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        }
        // Knight moves
        else if (piece == WN || piece == BN) {
            int knight_offsets[] = {-33, -31, -18, -14, 14, 18, 31, 33};
            for (int offset : knight_offsets) {
                int to = sq + offset;
                if (!(to & 0x88)) {
                    if (state.board[to] == EMPTY || get_color(state.board[to]) == them) {
                        list.push({sq, to, 0, 0});
                    }
                }
            }
        }
        // Sliding moves (Bishop, Rook, Queen)
        else if (piece == WB || piece == BB || piece == WR || piece == BR || piece == WQ || piece == BQ) {
            int offsets[8];
            int offset_count = 0;

            if (piece == WB || piece == BB) {
                offsets[0] = -17; offsets[1] = -15; offsets[2] = 15; offsets[3] = 17;
                offset_count = 4;
            } else if (piece == WR || piece == BR) {
                offsets[0] = -16; offsets[1] = -1; offsets[2] = 1; offsets[3] = 16;
                offset_count = 4;
            } else {
                offsets[0] = -17; offsets[1] = -16; offsets[2] = -15; offsets[3] = -1;
                offsets[4] = 1; offsets[5] = 15; offsets[6] = 16; offsets[7] = 17;
                offset_count = 8;
            }

            for (int i = 0; i < offset_count; ++i) {
                int offset = offsets[i];
                int to = sq + offset;
                while (!(to & 0x88)) {
                    if (state.board[to] == EMPTY) {
                        list.push({sq, to, 0, 0});
                    } else {
                        if (get_color(state.board[to]) == them) {
                            list.push({sq, to, 0, 0});
                        }
                        break;
                    }
                    to += offset;
                }
            }
        }
        // King moves & Castling
        else if (piece == WK || piece == BK) {
            int king_offsets[] = {-17, -16, -15, -1, 1, 15, 16, 17};
            for (int offset : king_offsets) {
                int to = sq + offset;
                if (!(to & 0x88)) {
                    if (state.board[to] == EMPTY || get_color(state.board[to]) == them) {
                        list.push({sq, to, 0, 0});
                    }
                }
            }

            if (us == WHITE && sq == 0x04) {
                if ((state.castling & 1) && state.board[0x05] == EMPTY && state.board[0x06] == EMPTY) {
                    if (!is_square_attacked(state, 0x04, BLACK) &&
                        !is_square_attacked(state, 0x05, BLACK) &&
                        !is_square_attacked(state, 0x06, BLACK)) {
                        list.push({0x04, 0x06, 0, 0});
                    }
                }
                if ((state.castling & 2) && state.board[0x03] == EMPTY && state.board[0x02] == EMPTY && state.board[0x01] == EMPTY) {
                    if (!is_square_attacked(state, 0x04, BLACK) &&
                        !is_square_attacked(state, 0x03, BLACK) &&
                        !is_square_attacked(state, 0x02, BLACK)) {
                        list.push({0x04, 0x02, 0, 0});
                    }
                }
            } else if (us == BLACK && sq == 0x74) {
                if ((state.castling & 4) && state.board[0x75] == EMPTY && state.board[0x76] == EMPTY) {
                    if (!is_square_attacked(state, 0x74, WHITE) &&
                        !is_square_attacked(state, 0x75, WHITE) &&
                        !is_square_attacked(state, 0x76, WHITE)) {
                        list.push({0x74, 0x76, 0, 0});
                    }
                }
                if ((state.castling & 8) && state.board[0x73] == EMPTY && state.board[0x72] == EMPTY && state.board[0x71] == EMPTY) {
                    if (!is_square_attacked(state, 0x74, WHITE) &&
                        !is_square_attacked(state, 0x73, WHITE) &&
                        !is_square_attacked(state, 0x72, WHITE)) {
                        list.push({0x74, 0x72, 0, 0});
                    }
                }
            }
        }
    }
}

// Generate capture moves only (for Quiescence Search)
void generate_captures(const BoardState& state, MoveList& list) {
    int us = state.side;
    int them = (us == WHITE) ? BLACK : WHITE;

    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece == EMPTY || get_color(piece) != us) continue;

        if (piece == WP) {
            int caps[] = {sq + 15, sq + 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (state.board[to_cap] != EMPTY && get_color(state.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 7) {
                            list.push({sq, to_cap, WQ, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == state.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        } else if (piece == BP) {
            int caps[] = {sq - 15, sq - 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (state.board[to_cap] != EMPTY && get_color(state.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 0) {
                            list.push({sq, to_cap, BQ, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == state.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        } else if (piece == WN || piece == BN) {
            int knight_offsets[] = {-33, -31, -18, -14, 14, 18, 31, 33};
            for (int offset : knight_offsets) {
                int to = sq + offset;
                if (!(to & 0x88)) {
                    if (state.board[to] != EMPTY && get_color(state.board[to]) == them) {
                        list.push({sq, to, 0, 0});
                    }
                }
            }
        } else if (piece == WB || piece == BB || piece == WR || piece == BR || piece == WQ || piece == BQ) {
            int offsets[8];
            int offset_count = 0;
            if (piece == WB || piece == BB) {
                offsets[0] = -17; offsets[1] = -15; offsets[2] = 15; offsets[3] = 17;
                offset_count = 4;
            } else if (piece == WR || piece == BR) {
                offsets[0] = -16; offsets[1] = -1; offsets[2] = 1; offsets[3] = 16;
                offset_count = 4;
            } else {
                offsets[0] = -17; offsets[1] = -16; offsets[2] = -15; offsets[3] = -1;
                offsets[4] = 1; offsets[5] = 15; offsets[6] = 16; offsets[7] = 17;
                offset_count = 8;
            }
            for (int i = 0; i < offset_count; ++i) {
                int offset = offsets[i];
                int to = sq + offset;
                while (!(to & 0x88)) {
                    if (state.board[to] != EMPTY) {
                        if (get_color(state.board[to]) == them) {
                            list.push({sq, to, 0, 0});
                        }
                        break;
                    }
                    to += offset;
                }
            }
        } else if (piece == WK || piece == BK) {
            int king_offsets[] = {-17, -16, -15, -1, 1, 15, 16, 17};
            for (int offset : king_offsets) {
                int to = sq + offset;
                if (!(to & 0x88)) {
                    if (state.board[to] != EMPTY && get_color(state.board[to]) == them) {
                        list.push({sq, to, 0, 0});
                    }
                }
            }
        }
    }
}

// Make a move and incrementally update the Zobrist Hash
bool make_move(const BoardState& current, BoardState& next, const Move& move) {
    next = current;

    int from = move.from;
    int to = move.to;
    int piece = next.board[from];
    int victim = next.board[to];

    // Incremental hash setup: remove state dependencies
    next.hash ^= side_key;
    next.hash ^= castle_keys[current.castling];
    if (current.enpassant != -1) {
        next.hash ^= ep_keys[current.enpassant];
    }

    // XOR out moving piece and captured piece
    next.hash ^= piece_keys[piece][from];
    if (victim != EMPTY) {
        next.hash ^= piece_keys[victim][to];
    }

    // En Passant Capture
    if ((piece == WP || piece == BP) && to == next.enpassant) {
        int ep_pawn_sq = (piece == WP) ? (to - 16) : (to + 16);
        next.hash ^= piece_keys[next.board[ep_pawn_sq]][ep_pawn_sq];
        next.board[ep_pawn_sq] = EMPTY;
    }

    // Castling updates
    if (piece == WK && from == 0x04) {
        if (to == 0x06) {
            next.board[0x05] = WR; next.board[0x07] = EMPTY;
            next.hash ^= piece_keys[WR][0x05] ^ piece_keys[WR][0x07];
        } else if (to == 0x02) {
            next.board[0x03] = WR; next.board[0x00] = EMPTY;
            next.hash ^= piece_keys[WR][0x03] ^ piece_keys[WR][0x00];
        }
    } else if (piece == BK && from == 0x74) {
        if (to == 0x76) {
            next.board[0x75] = BR; next.board[0x77] = EMPTY;
            next.hash ^= piece_keys[BR][0x75] ^ piece_keys[BR][0x77];
        } else if (to == 0x72) {
            next.board[0x73] = BR; next.board[0x70] = EMPTY;
            next.hash ^= piece_keys[BR][0x73] ^ piece_keys[BR][0x70];
        }
    }

    // Update castling rights
    if (piece == WK) next.castling &= ~3;
    if (piece == BK) next.castling &= ~12;
    if (from == 0x00 || to == 0x00) next.castling &= ~2;
    if (from == 0x07 || to == 0x07) next.castling &= ~1;
    if (from == 0x70 || to == 0x70) next.castling &= ~8;
    if (from == 0x77 || to == 0x77) next.castling &= ~4;

    // Execute standard move
    next.board[to] = piece;
    next.board[from] = EMPTY;

    if (move.promoted != 0) {
        next.board[to] = move.promoted;
        next.hash ^= piece_keys[piece][to] ^ piece_keys[move.promoted][to];
    } else {
        next.hash ^= piece_keys[piece][to];
    }

    // En Passant square setup
    next.enpassant = -1;
    if (piece == WP && (to - from == 32)) {
        next.enpassant = from + 16;
    } else if (piece == BP && (from - to == 32)) {
        next.enpassant = from - 16;
    }

    // Hash in new dependencies
    next.hash ^= castle_keys[next.castling];
    if (next.enpassant != -1) {
        next.hash ^= ep_keys[next.enpassant];
    }

    // Verify move legality (cannot leave king in check)
    int us = next.side;
    int them = (us == WHITE) ? BLACK : WHITE;

    int king_sq = -1;
    int target_king = (us == WHITE) ? WK : BK;
    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        if (next.board[sq] == target_king) {
            king_sq = sq;
            break;
        }
    }

    if (king_sq == -1 || is_square_attacked(next, king_sq, them)) {
        return false; // Illegal move
    }

    next.side = them;
    return true;
}

// Master-level Evaluation Heuristics
int evaluate(const BoardState& state) {
    int score = 0;
    int active_pieces = 0;

    // Double pawns tracking
    int white_pawn_count[8] = {0};
    int black_pawn_count[8] = {0};

    int white_bishops = 0;
    int black_bishops = 0;

    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece == EMPTY) continue;

        if (piece != WP && piece != BP && piece != WK && piece != BK) {
            active_pieces++;
        }

        if (piece == WB) white_bishops++;
        if (piece == BB) black_bishops++;
        if (piece == WP) white_pawn_count[sq & 7]++;
        if (piece == BP) black_pawn_count[sq & 7]++;
    }

    bool endgame = (active_pieces <= 2);

    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece == EMPTY) continue;

        int color = get_color(piece);
        int val = piece_values[piece];

        // Perspective flipped PST indexes
        int pst_idx = (color == WHITE) ? ((7 - (sq >> 4)) * 8 + (sq & 7)) : ((sq >> 4) * 8 + (sq & 7));
        int pst_val = 0;

        switch (piece) {
            case WP: pst_val = pawn_table[pst_idx]; break;
            case BP: pst_val = pawn_table[pst_idx]; break;
            case WN: pst_val = knight_table[pst_idx]; break;
            case BN: pst_val = knight_table[pst_idx]; break;
            case WB: pst_val = bishop_table[pst_idx]; break;
            case BB: pst_val = bishop_table[pst_idx]; break;
            case WR: pst_val = rook_table[pst_idx]; break;
            case BR: pst_val = rook_table[pst_idx]; break;
            case WQ: pst_val = queen_table[pst_idx]; break;
            case BQ: pst_val = queen_table[pst_idx]; break;
            case WK: pst_val = endgame ? king_end_table[pst_idx] : king_middle_table[pst_idx]; break;
            case BK: pst_val = endgame ? king_end_table[pst_idx] : king_middle_table[pst_idx]; break;
        }

        if (color == WHITE) {
            score += val + pst_val;
        } else {
            score -= (val + pst_val);
        }
    }

    // Bishop pair bonuses (essential for high level strategy)
    if (white_bishops >= 2) score += 30;
    if (black_bishops >= 2) score -= 30;

    // Double pawns penalty
    for (int f = 0; f < 8; ++f) {
        if (white_pawn_count[f] > 1) score -= 20 * (white_pawn_count[f] - 1);
        if (black_pawn_count[f] > 1) score += 20 * (black_pawn_count[f] - 1);
    }

    return (state.side == WHITE) ? score : -score;
}

// Check search elapsed time
void check_time() {
    if (nodes_searched % 2048 == 0) {
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration<double, std::milli>(now - search_start).count();
        if (elapsed >= search_time_limit_ms) {
            search_stopped = true;
        }
    }
}

// MVV-LVA move scoring, incorporating killer moves and PV moves
void score_moves(const BoardState& state, MoveList& list, const Move& pv_move, int ply) {
    for (int i = 0; i < list.count; ++i) {
        Move& m = list.moves[i];
        if (m == pv_move) {
            m.score = 2000000;
            continue;
        }

        int attacker = state.board[m.from];
        int victim = state.board[m.to];

        if (victim != EMPTY) {
            m.score = 100000 + (piece_values[victim] * 10) - piece_values[attacker];
        } else if (m.promoted != 0) {
            m.score = 90000 + piece_values[m.promoted];
        } else if (ply < 64 && m == killer_moves[0][ply]) {
            m.score = 80000;
        } else if (ply < 64 && m == killer_moves[1][ply]) {
            m.score = 70000;
        } else {
            m.score = 0;
        }
    }
}

void sort_moves(MoveList& list, int current_index) {
    for (int i = current_index + 1; i < list.count; ++i) {
        if (list.moves[i].score > list.moves[current_index].score) {
            std::swap(list.moves[i], list.moves[current_index]);
        }
    }
}

// Quiescence Search to avoid the horizon effect
int quiescence(const BoardState& state, int alpha, int beta) {
    check_time();
    if (search_stopped) return 0;

    nodes_searched++;

    int stand_pat = evaluate(state);
    if (stand_pat >= beta) return beta;
    if (stand_pat > alpha) alpha = stand_pat;

    MoveList list;
    generate_captures(state, list);
    score_moves(state, list, {0, 0, 0, 0}, 0);

    for (int i = 0; i < list.count; ++i) {
        sort_moves(list, i);
        const Move& m = list.moves[i];

        BoardState next;
        if (!make_move(state, next, m)) continue;

        int score = -quiescence(next, -beta, -alpha);
        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
    }

    return alpha;
}

// Principal Alpha-Beta Search with Transposition Table, Killer Moves, and Null Move Pruning
int search(const BoardState& state, int depth, int ply, int alpha, int beta, Move& best_move, const Move& pv_move) {
    check_time();
    if (search_stopped) return 0;

    nodes_searched++;

    if (ply > 64) return evaluate(state);
    if (depth == 0) return quiescence(state, alpha, beta);

    // 1. Probe the Transposition Table (Engine Memory)
    int tt_score = 0;
    Move tt_move = {0, 0, 0, 0};
    if (tt_probe(state.hash, depth, ply, alpha, beta, tt_score, tt_move)) {
        best_move = tt_move;
        return tt_score;
    }

    bool in_check = is_in_check(state);

    // 2. Null Move Pruning (Deep search bypass heuristic)
    if (!in_check && depth >= 3 && has_non_pawn_material(state, state.side)) {
        BoardState null_state = state;
        null_state.side = (state.side == WHITE) ? BLACK : WHITE;
        null_state.enpassant = -1;

        // Update hash for passing active side
        null_state.hash ^= side_key;
        if (state.enpassant != -1) {
            null_state.hash ^= ep_keys[state.enpassant];
        }

        Move dummy_move = {0, 0, 0, 0};
        int reduction = 2; // Search reduction factor
        int score = -search(null_state, depth - 1 - reduction, ply + 1, -beta, -beta + 1, dummy_move, {0, 0, 0, 0});

        if (score >= beta) {
            return beta; // Prune branch
        }
    }

    MoveList list;
    generate_moves(state, list);

    // Prioritize the TT move or PV move to optimize Alpha-Beta cuts
    Move primary_ordering_move = (tt_move.from != 0 || tt_move.to != 0) ? tt_move : pv_move;
    score_moves(state, list, primary_ordering_move, ply);

    int legal_moves = 0;
    int best_score = -1000000;
    Move local_best_move = {0, 0, 0, 0};
    int orig_alpha = alpha;

    for (int i = 0; i < list.count; ++i) {
        sort_moves(list, i);
        const Move& m = list.moves[i];

        BoardState next;
        if (!make_move(state, next, m)) continue;

        legal_moves++;
        Move temp_move = {0, 0, 0, 0};
        int score = -search(next, depth - 1, ply + 1, -beta, -alpha, temp_move, {0, 0, 0, 0});

        if (score > best_score) {
            best_score = score;
            local_best_move = m;
        }

        // Beta cutoff found
        if (score >= beta) {
            // Save to killer moves to order future quiet sibling nodes
            if (state.board[m.to] == EMPTY) {
                store_killer(m, ply);
            }
            tt_store(state.hash, depth, ply, TT_BETA, beta, m);
            best_move = m;
            return beta;
        }
        if (score > alpha) {
            alpha = score;
        }
    }

    // Checkmate & Stalemate detection
    if (legal_moves == 0) {
        if (in_check) {
            return -30000 + ply; // Return mate score adjusted by path length
        } else {
            return 0; // Stalemate
        }
    }

    // Save final search result in the Transposition Table
    int flag = (alpha <= orig_alpha) ? TT_ALPHA : TT_EXACT;
    tt_store(state.hash, depth, ply, flag, alpha, local_best_move);

    best_move = local_best_move;
    return alpha;
}

// Iterative Deepening
Move iterative_deepening(const BoardState& state, double time_limit_ms) {
    search_start = std::chrono::steady_clock::now();
    search_time_limit_ms = time_limit_ms;
    search_stopped = false;
    nodes_searched = 0;

    Move last_completed_best_move = {0, 0, 0, 0};

    // Emergency fallback move (first legal one)
    MoveList list;
    generate_moves(state, list);
    for (int i = 0; i < list.count; ++i) {
        BoardState next;
        if (make_move(state, next, list.moves[i])) {
            last_completed_best_move = list.moves[i];
            break;
        }
    }

    for (int depth = 1; depth <= 12; ++depth) {
        Move current_best_move = {0, 0, 0, 0};
        int score = search(state, depth, 0, -1000000, 1000000, current_best_move, last_completed_best_move);

        if (search_stopped) break;

        last_completed_best_move = current_best_move;

        auto now = std::chrono::steady_clock::now();
        double elapsed_ms = std::chrono::duration<double, std::milli>(now - search_start).count();
        double nps = (elapsed_ms > 0) ? (nodes_searched / (elapsed_ms / 1000.0)) : 0;

        // Print search feedback in standard UCI format for Arena/GUIs
        std::cout << "info depth " << depth << " score cp " << score
                  << " nodes " << nodes_searched << " nps " << (int)nps
                  << " time " << (int)elapsed_ms << " pv "
                  << square_to_uci(last_completed_best_move.from)
                  << square_to_uci(last_completed_best_move.to);
        if (last_completed_best_move.promoted != 0) {
            std::cout << piece_to_promotion_char(last_completed_best_move.promoted);
        }
        std::cout << std::endl;

        if (score > 25000 || score < -25000) break; // Checkmate found
    }

    return last_completed_best_move;
}

// Load position from FEN string
void load_fen(BoardState& state, const std::string& fen) {
    for (int i = 0; i < 128; ++i) state.board[i] = EMPTY;
    state.side = WHITE;
    state.castling = 0;
    state.enpassant = -1;

    std::stringstream ss(fen);
    std::string board_part, active_part, castle_part, ep_part;
    ss >> board_part >> active_part >> castle_part >> ep_part;

    int rank = 7;
    int file = 0;
    for (char c : board_part) {
        if (c == '/') {
            rank--; file = 0;
        } else if (isdigit(c)) {
            file += (c - '0');
        } else {
            int piece = EMPTY;
            switch (c) {
                case 'P': piece = WP; break;
                case 'N': piece = WN; break;
                case 'B': piece = WB; break;
                case 'R': piece = WR; break;
                case 'Q': piece = WQ; break;
                case 'K': piece = WK; break;
                case 'p': piece = BP; break;
                case 'n': piece = BN; break;
                case 'b': piece = BB; break;
                case 'r': piece = BR; break;
                case 'q': piece = BQ; break;
                case 'k': piece = BK; break;
            }
            int sq = (rank << 4) + file;
            state.board[sq] = piece;
            file++;
        }
    }

    if (active_part == "b") state.side = BLACK;

    for (char c : castle_part) {
        if (c == 'K') state.castling |= 1;
        if (c == 'Q') state.castling |= 2;
        if (c == 'k') state.castling |= 4;
        if (c == 'q') state.castling |= 8;
    }

    if (ep_part != "-" && ep_part.length() >= 2) {
        state.enpassant = uci_to_square(ep_part);
    }

    state.hash = generate_hash(state);
}

// Parse position updates
void parse_position(BoardState& state, const std::string& cmd) {
    std::stringstream ss(cmd);
    std::string dummy, type;
    ss >> dummy >> type;

    if (type == "startpos") {
        load_fen(state, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    } else if (type == "fen") {
        std::string fen_string = "";
        std::string part;
        for (int i = 0; i < 6; ++i) {
            ss >> part; fen_string += part + " ";
        }
        load_fen(state, fen_string);
    }

    std::string moves_token;
    if (ss >> moves_token && moves_token == "moves") {
        std::string move_str;
        while (ss >> move_str) {
            MoveList list;
            generate_moves(state, list);
            for (int i = 0; i < list.count; ++i) {
                Move m = list.moves[i];
                std::string current_m_str = square_to_uci(m.from) + square_to_uci(m.to);
                if (m.promoted != 0) {
                    current_m_str += piece_to_promotion_char(m.promoted);
                }
                if (current_m_str == move_str) {
                    BoardState next;
                    if (make_move(state, next, m)) {
                        state = next;
                        break;
                    }
                }
            }
        }
    }
}

// Parse 'go' commands and allocate search time budget
void parse_go(const BoardState& state, const std::string& cmd) {
    std::stringstream ss(cmd);
    std::string token;
    ss >> token;

    int depth_limit = 100;
    double time_limit_ms = 2000.0; // Default fallback to 2 seconds

    int wtime = -1, btime = -1;
    int winc = 0, binc = 0;
    int movestogo = 40;

    while (ss >> token) {
        if (token == "depth") {
            ss >> depth_limit;
            time_limit_ms = 1000000.0; // Allow it to search safely to target depth
        } else if (token == "wtime") {
            ss >> wtime;
        } else if (token == "btime") {
            ss >> btime;
        } else if (token == "winc") {
            ss >> winc;
        } else if (token == "binc") {
            ss >> binc;
        } else if (token == "movestogo") {
            ss >> movestogo;
        }
    }

    if (state.side == WHITE && wtime != -1) {
        time_limit_ms = (double)wtime / movestogo + (double)winc * 0.8;
        if (time_limit_ms < 100) time_limit_ms = 100;
    } else if (state.side == BLACK && btime != -1) {
        time_limit_ms = (double)btime / movestogo + (double)binc * 0.8;
        if (time_limit_ms < 100) time_limit_ms = 100;
    }

    Move best = iterative_deepening(state, time_limit_ms);

    std::cout << "bestmove " << square_to_uci(best.from) << square_to_uci(best.to);
    if (best.promoted != 0) {
        std::cout << piece_to_promotion_char(best.promoted);
    }
    std::cout << std::endl;
}

int main() {
    // Standard line-buffering to ensure instant Arena communication
    std::setvbuf(stdout, NULL, _IOLBF, 0);

    init_zobrist();
    init_tt();

    BoardState state;
    load_fen(state, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");

    std::string line;
    while (std::getline(std::cin, line)) {
        if (line.empty()) continue;
        std::stringstream ss(line);
        std::string cmd;
        ss >> cmd;

        if (cmd == "uci") {
            std::cout << "id name IM_Engine_2000" << std::endl;
            std::cout << "id author ChessAI" << std::endl;
            std::cout << "uciok" << std::endl;
        } else if (cmd == "isready") {
            std::cout << "readyok" << std::endl;
        } else if (cmd == "ucinewgame") {
            clear_tt();
            load_fen(state, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
        } else if (cmd == "position") {
            parse_position(state, line);
        } else if (cmd == "go") {
            parse_go(state, line);
        } else if (cmd == "quit") {
            break;
        }
    }

    if (transposition_table) delete[] transposition_table;
    return 0;
}
