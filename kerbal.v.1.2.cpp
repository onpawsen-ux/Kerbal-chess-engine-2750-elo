#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>
#include <chrono>
#include <cctype>
#include <cstring>
#include <random>
#include <map>
#include <fstream>

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

// History moves for quiet move ordering
int history_moves[13][128];

// Global Opening Book Databases
std::vector<std::string> uci_moves_played;
std::map<std::vector<std::string>, std::vector<std::string>> opening_book;

// PeSTO Piece Values for Tapered Evaluation
const int mg_value[] = { 0, 82, 337, 365, 477, 1025, 0, 82, 337, 365, 477, 1025, 0 };
const int eg_value[] = { 0, 94, 281, 297, 512,  936, 0, 94, 281, 297, 512,  936, 0 };

// PeSTO Piece-Square Tables (PST)
const int mg_pawn_table[64] = {
      0,   0,   0,   0,   0,   0,   0,   0,
     98, 134,  61,  95,  68, 126,  34, -11,
     -6,   7,  26,  31,  65,  56,  25, -20,
    -14,  13,   6,  21,  17,  12,   0, -16,
    -27,  -2,  -5,  12,  17,   6,  10, -17,
    -26,  -4,  -4, -10,   3,   3,  33, -12,
    -35,  -1, -20, -23, -15,  24,  38, -22,
      0,   0,   0,   0,   0,   0,   0,   0
};
const int eg_pawn_table[64] = {
      0,   0,   0,   0,   0,   0,   0,   0,
    178, 173, 158, 134, 147, 180, 165, 165,
     94, 100,  85,  67,  56,  53,  82,  84,
     32,  32,  28,  18,  10,  12,  33,  28,
     -9,   4,   4,  -3,  -6, -13, -13, -20,
    -13,  -1, -10,  -8,  -1, -11, -10, -22,
    -14,   5,  -3,  -1,  -7, -15, -12, -18,
      0,   0,   0,   0,   0,   0,   0,   0
};

const int mg_knight_table[64] = {
    -167, -89, -34, -49,  61, -97, -15, -107,
     -73, -41,  72,  36,  23,  62,   7,  -17,
     -47,  60,  37,  65,  84, 129,  73,   44,
      -9,  17,  19,  53,  37,  69,  18,   22,
     -13,   4,  16,  13,  28,  19,  21,   -8,
     -23, -15,   7,  -1,  10,  14, -16,  -20,
     -62,  12, -11, -13,  -1,  -9,  13,  -30,
    -105, -74, -58, -33, -17, -28, -61,  -54
};
const int eg_knight_table[64] = {
    -58, -38, -13, -28, -31, -27, -63, -99,
    -25,  -8, -25,  -2,  -9, -25, -24, -28,
    -11,  15,   1,  15,  15,  -1, -15, -23,
     -5,   5,  17,  10,  14,  15,  -1,  -9,
     -18,  -4,   8,  10,   8,   1,  -2, -17,
     -17, -18, -18,  -1,  -5, -15, -13, -30,
     -31, -27, -15, -11, -13, -16, -17, -48,
     -51, -27, -27, -22, -22, -28, -51, -51
};

const int mg_bishop_table[64] = {
    -29,   4, -18, -10, -18, -23, -20, -36,
    -12,  19,  12,  -4,   9,  22,  16,  -5,
     -4,  13,  19,  27,  10,  29,  19,  -3,
     -1,   9,  28,  30,  56,  34,  11,  -2,
     -4,  17,  15,  35,  37,  34,   9, -14,
    -13,  -2,  16,  -6,  -1,  -7,   6,  -6,
     -4,  17, -11, -12, -22, -22,   8,  -9,
    -23, -14, -23, -21, -16, -16, -15, -24
};
const int eg_bishop_table[64] = {
    -14,  -9, -15, -14, -13, -10, -22, -29,
     -3,  -7,  -8,  -3,  -8,  -7,  -4, -12,
     -3,   5,  -3,  -4,   0,  -4,  -3, -15,
     -3,   3,  -1,  -1,   7,   1,  -4,  -9,
     -4,   5,  -2,  -7,  -5,  -8, -10, -17,
    -10,  -1,  -6,  -7,   2,  -2,  -1, -12,
     -8,  -4,  -7, -14,  -9, -11,  -9, -15,
    -14, -13, -13, -14, -13, -14, -13, -16
};

const int mg_rook_table[64] = {
     32,  42,  32,  51,  63,   9,  31,  43,
     27,  32,  58,  62,  80,  67,  26,  44,
     -5,  19,  26,  36,  17,  45,  61,  16,
    -15, -11,  13,  24,  15,  19,  -6, -10,
    -16, -11,  -9,   7,  21,  -2, -11, -20,
    -22, -18, -22, -22,  -5, -18, -18, -22,
    -17, -19, -18,  -5,  -1,  -9, -20, -20,
     -9, -13,  -8,   4,   4,  -6, -10, -13
};
const int eg_rook_table[64] = {
     13,  10,  18,  15,  12,  12,   8,   5,
     11,  13,  13,  14,  -3,   4,   7,  -6,
      7,   7,   7,   5,   4,  -3,  -5, -14,
      4,   3,  13,   1,   2,   1,  -1,  -2,
      3,   5,   8,   4,   7,   6,   1,  -4,
     -3,  -6,   0,  -5,  -1,  -6,  -5,  -7,
     -3,  -1,  -4,  -7,  -7,  -8,  -5,  -6,
     -3,  -5,   0,  -5,  -5,  -5,  -9,  -9
};

const int mg_queen_table[64] = {
    -28,   0,  29,  12,  34,  44,  44,  10,
    -16, -18,  -9,  24,  39,  25,  -6,  19,
    -26,  -3,  -7,  14,  19,  11,  16, -13,
     -9, -15,  -9,   7,   8,  -5, -10, -22,
    -14, -13, -10,  -1,  -1,  -9, -15, -14,
    -18,  -7,  -6,  -8,  -3, -11, -10, -18,
    -23,  -3, -19, -21, -17, -17, -24, -23,
    -25, -23, -25, -24, -25, -24, -23, -25
};
const int eg_queen_table[64] = {
     -9, -26,  -9, -11, -11, -16, -23, -33,
      4, -16,  -4, -14,  -9, -15,  -3, -15,
     -8,  -5,   2,  -6,  -2,  -1,   1, -14,
      1,  10,   2,   3,   3,  11,   7,  -7,
         -5,  10,  12,   9,  11,  15,  10,  -2,
         -6,   2,   2,   3,   5,   1,   1, -14,
         -7,  -2,  -6,  -1,  -2,  -5,  -1,  -9,
        -24, -11, -21, -10, -10, -17, -14, -22
};

const int mg_king_table[64] = {
    -210, -118,  -86, -118, -120,  -84, -115, -195,
    -110,  -65,  -59,  -61,  -60,  -51,  -54, -108,
     -76,  -37,  -44,  -53,  -47,  -38,  -33,  -73,
     -45,  -24,  -25,  -37,  -38,  -21,  -19,  -45,
     -13,    6,    6,  -13,  -13,    6,    6,  -13,
      10,   30,   10,  -10,  -10,   10,   30,   10,
      52,   52,   27,   11,   11,   27,   52,   52,
      76,   91,   60,   37,   37,   60,   91,   76
};
const int eg_king_table[64] = {
    -53, -34, -21, -11, -11, -21, -34, -53,
    -34, -15,  -2,   8,   8,  -2, -15, -34,
    -21,  -2,  11,  21,  21,  11,  -2, -21,
    -11,   8,  21,  30,  30,  21,   8, -11,
    -11,   8,  21,  30,  30,  21,   8, -11,
    -21,  -2,  11,  21,  21,  11,  -2, -21,
    -34, -15,  -2,   8,   8,  -2, -15, -34,
    -53, -34, -21, -11, -11, -21, -34, -53
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

void clear_history() {
    // Decay history values instead of clear to preserve context across iterations
    for (int p = 0; p < 13; ++p) {
        for (int sq = 0; sq < 128; ++sq) {
            history_moves[p][sq] /= 2;
        }
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

// Checks if player has sacrificed their queen
bool is_queen_sacrificed(const BoardState& state) {
    int us = state.side;
    int our_queens = 0;
    int their_queens = 0;
    int our_other_pieces = 0;

    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece == EMPTY) continue;

        int color = get_color(piece);
        if (color == us) {
            if (piece == WQ || piece == BQ) {
                our_queens++;
            } else if (piece != WP && piece != BP && piece != WK && piece != BK) {
                our_other_pieces++;
            }
        } else {
            if (piece == WQ || piece == BQ) {
                their_queens++;
            }
        }
    }
    return (our_queens == 0 && their_queens > 0 && our_other_pieces > 0);
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

// Helper to determine if a legal move matches a PGN/SAN string
bool move_matches_san(const BoardState& state, const Move& m, std::string san) {
    if (san.empty()) return false;

    // Strip check/mate symbols (+, #)
    if (san.back() == '+' || san.back() == '#') {
        san.pop_back();
    }

    int piece = state.board[m.from];
    int piece_type = piece;
    int us = state.side;

    // Castling
    if (san == "O-O" || san == "0-0") {
        if (us == WHITE) {
            return (piece_type == WK && m.from == 0x04 && m.to == 0x06);
        } else {
            return (piece_type == BK && m.from == 0x74 && m.to == 0x76);
        }
    }
    if (san == "O-O-O" || san == "0-0-0") {
        if (us == WHITE) {
            return (piece_type == WK && m.from == 0x04 && m.to == 0x02);
        } else {
            return (piece_type == BK && m.from == 0x74 && m.to == 0x72);
        }
    }

    // Parse promotions (e.g. e8=Q or e8Q)
    int promo_piece = 0;
    size_t equal_sign = san.find('=');
    if (equal_sign != std::string::npos) {
        char p_char = san[equal_sign + 1];
        san = san.substr(0, equal_sign);
        if (us == WHITE) {
            if (p_char == 'Q') promo_piece = WQ;
            else if (p_char == 'R') promo_piece = WR;
            else if (p_char == 'B') promo_piece = WB;
            else if (p_char == 'N') promo_piece = WN;
        } else {
            if (p_char == 'Q') promo_piece = BQ;
            else if (p_char == 'R') promo_piece = BR;
            else if (p_char == 'B') promo_piece = BB;
            else if (p_char == 'N') promo_piece = BN;
        }
    } else {
        if (!san.empty() && isupper(san.back()) && (piece_type == WP || piece_type == BP)) {
            char p_char = san.back();
            san.pop_back();
            if (us == WHITE) {
                if (p_char == 'Q') promo_piece = WQ;
                else if (p_char == 'R') promo_piece = WR;
                else if (p_char == 'B') promo_piece = WB;
                else if (p_char == 'N') promo_piece = WN;
            } else {
                if (p_char == 'Q') promo_piece = BQ;
                else if (p_char == 'R') promo_piece = BR;
                else if (p_char == 'B') promo_piece = BB;
                else if (p_char == 'N') promo_piece = BN;
            }
        }
    }

    if (m.promoted != promo_piece) return false;

    // Strip capture indicators ('x')
    size_t x_pos = san.find('x');
    if (x_pos != std::string::npos) {
        san.erase(x_pos, 1);
    }

    // Determine targeted piece type
    char san_piece_char = san[0];
    int target_piece_type = EMPTY;
    bool is_pawn = false;

    if (san_piece_char == 'N') target_piece_type = (us == WHITE) ? WN : BN;
    else if (san_piece_char == 'B') target_piece_type = (us == WHITE) ? WB : BB;
    else if (san_piece_char == 'R') target_piece_type = (us == WHITE) ? WR : BR;
    else if (san_piece_char == 'Q') target_piece_type = (us == WHITE) ? WQ : BQ;
    else if (san_piece_char == 'K') target_piece_type = (us == WHITE) ? WK : BK;
    else {
        is_pawn = true;
        target_piece_type = (us == WHITE) ? WP : BP;
    }

    if (piece_type != target_piece_type) return false;

    std::string rest = is_pawn ? san : san.substr(1);
    if (rest.length() < 2) return false;

    // Last 2 characters must represent the destination square
    std::string target_sq_str = rest.substr(rest.length() - 2);
    int dest_sq = uci_to_square(target_sq_str);
    if (m.to != dest_sq) return false;

    // Disambiguate files and ranks (e.g. Nbd2, N1f3)
    std::string disambig = rest.substr(0, rest.length() - 2);
    if (!disambig.empty()) {
        char file_disambig = ' ';
        char rank_disambig = ' ';
        if (disambig.length() == 1) {
            if (disambig[0] >= 'a' && disambig[0] <= 'h') {
                file_disambig = disambig[0];
            } else if (disambig[0] >= '1' && disambig[0] <= '8') {
                rank_disambig = disambig[0];
            }
        } else if (disambig.length() == 2) {
            file_disambig = disambig[0];
            rank_disambig = disambig[1];
        }

        int from_file = 'a' + (m.from & 7);
        int from_rank = '1' + (m.from >> 4);

        if (file_disambig != ' ' && from_file != file_disambig) return false;
        if (rank_disambig != ' ' && from_rank != rank_disambig) return false;
    }

    BoardState next;
    return make_move(state, next, m);
}

// Tokenize PGN formats into pure SAN move string tokens
std::vector<std::string> parse_pgn_to_san(const std::string& pgn) {
    std::vector<std::string> san_moves;
    std::stringstream ss(pgn);
    std::string token;
    while (ss >> token) {
        if (token.find('.') != std::string::npos) {
            size_t dot_pos = token.find_last_of('.');
            if (dot_pos != std::string::npos && dot_pos < token.length() - 1) {
                std::string actual_move = token.substr(dot_pos + 1);
                if (!actual_move.empty()) {
                    san_moves.push_back(actual_move);
                }
            }
            continue;
        }
        san_moves.push_back(token);
    }
    return san_moves;
}

// Simulates a sequence of SAN moves on an initial board state to produce a coordinate move sequence
std::vector<std::string> san_to_uci_sequence(const std::vector<std::string>& san_moves) {
    BoardState temp_state;
    // Standard starting FEN
    for (int i = 0; i < 128; ++i) temp_state.board[i] = EMPTY;
    temp_state.side = WHITE;
    temp_state.castling = 15;
    temp_state.enpassant = -1;

    std::string board_part = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR";
    int rank = 7, file = 0;
    for (char c : board_part) {
        if (c == '/') { rank--; file = 0; }
        else if (isdigit(c)) { file += (c - '0'); }
        else {
            int piece = EMPTY;
            switch (c) {
                case 'P': piece = WP; break; case 'N': piece = WN; break;
                case 'B': piece = WB; break; case 'R': piece = WR; break;
                case 'Q': piece = WQ; break; case 'K': piece = WK; break;
                case 'p': piece = BP; break; case 'n': piece = BN; break;
                case 'b': piece = BB; break; case 'r': piece = BR; break;
                case 'q': piece = BQ; break; case 'k': piece = BK; break;
            }
            temp_state.board[(rank << 4) + file] = piece;
            file++;
        }
    }
    temp_state.hash = generate_hash(temp_state);

    std::vector<std::string> uci_seq;
    for (const std::string& san : san_moves) {
        MoveList list;
        generate_moves(temp_state, list);
        Move matched_move = {0, 0, 0, 0};
        bool found = false;

        for (int i = 0; i < list.count; ++i) {
            Move m = list.moves[i];
            if (move_matches_san(temp_state, m, san)) {
                matched_move = m;
                found = true;
                break;
            }
        }

        if (!found) return {}; // Abort if parsing error or illegal moves are found in DB

        std::string uci_str = square_to_uci(matched_move.from) + square_to_uci(matched_move.to);
        if (matched_move.promoted != 0) {
            uci_str += piece_to_promotion_char(matched_move.promoted);
        }
        uci_seq.push_back(uci_str);

        BoardState next;
        if (!make_move(temp_state, next, matched_move)) return {};
        temp_state = next;
    }
    return uci_seq;
}

// Parses open file database and loads the transposition mapping
void load_opening_book() {
    std::ifstream file("chess_openings_comprehensive.txt");
    if (!file.is_open()) {
        return;
    }

    std::string line;
    // Skip headers
    std::getline(file, line);

    while (std::getline(file, line)) {
        if (line.empty()) continue;

        std::vector<std::string> tokens;
        size_t start = 0;
        size_t end = line.find('\t');
        while (end != std::string::npos) {
            tokens.push_back(line.substr(start, end - start));
            start = end + 1;
            end = line.find('\t', start);
        }
        tokens.push_back(line.substr(start));

        if (tokens.size() < 3) continue;

        std::string pgn = tokens[2];
        if (pgn.empty()) continue;

        std::vector<std::string> san_moves = parse_pgn_to_san(pgn);
        std::vector<std::string> uci_moves = san_to_uci_sequence(san_moves);

        if (uci_moves.empty()) continue;

        std::vector<std::string> path;
        for (size_t i = 0; i < uci_moves.size(); ++i) {
            std::string next_move = uci_moves[i];
            auto& move_list = opening_book[path];
            if (std::find(move_list.begin(), move_list.end(), next_move) == move_list.end()) {
                move_list.push_back(next_move);
            }
            path.push_back(next_move);
        }
    }
}

// PeSTO Tapered Evaluation
int evaluate(const BoardState& state) {
    int mg[2] = {0, 0};
    int eg[2] = {0, 0};
    int phase = 0;

    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = state.board[sq];
        if (piece == EMPTY) continue;

        int color = get_color(piece);
        int r = sq >> 4;
        int f = sq & 7;
        int idx = r * 8 + f;
        if (color == WHITE) {
            idx = (7 - r) * 8 + f; // Flip vertically for white perspective
        }

        // Accumulate phase values
        switch (piece) {
            case WN: case BN: phase += 1; break;
            case WB: case BB: phase += 1; break;
            case WR: case BR: phase += 2; break;
            case WQ: case BQ: phase += 4; break;
        }

        int mg_val = mg_value[piece];
        int eg_val = eg_value[piece];

        switch (piece) {
            case WP: case BP: mg_val += mg_pawn_table[idx]; eg_val += eg_pawn_table[idx]; break;
            case WN: case BN: mg_val += mg_knight_table[idx]; eg_val += eg_knight_table[idx]; break;
            case WB: case BB: mg_val += mg_bishop_table[idx]; eg_val += eg_bishop_table[idx]; break;
            case WR: case BR: mg_val += mg_rook_table[idx]; eg_val += eg_rook_table[idx]; break;
            case WQ: case BQ: mg_val += mg_queen_table[idx]; eg_val += eg_queen_table[idx]; break;
            case WK: case BK: mg_val += mg_king_table[idx]; eg_val += eg_king_table[idx]; break;
        }

        mg[color] += mg_val;
        eg[color] += eg_val;
    }

    if (phase > 24) phase = 24;

    int mg_score = mg[WHITE] - mg[BLACK];
    int eg_score = eg[WHITE] - eg[BLACK];

    // Smooth interpolation between midgame and endgame
    int score = ((mg_score * phase) + (eg_score * (24 - phase))) / 24;

    // Bishop pair bonuses
    int white_bishops = 0, black_bishops = 0;
    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        if (state.board[sq] == WB) white_bishops++;
        if (state.board[sq] == BB) black_bishops++;
    }
    if (white_bishops >= 2) score += 30;
    if (black_bishops >= 2) score -= 30;

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

// MVV-LVA move scoring, incorporating killer moves, history moves, and PV moves
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
            m.score = 100000 + (mg_value[victim] * 10) - mg_value[attacker];
        } else if (m.promoted != 0) {
            m.score = 90000 + mg_value[m.promoted];
        } else if (ply < 64 && m == killer_moves[0][ply]) {
            m.score = 80000;
        } else if (ply < 64 && m == killer_moves[1][ply]) {
            m.score = 70000;
        } else {
            m.score = history_moves[attacker][m.to];
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

// Principal Alpha-Beta Search with Transposition Table, Killer Moves, History Heuristics, and Late Move Reduction
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
    bool pv_node = (beta - alpha > 1);
    bool queen_sacced = is_queen_sacrificed(state);

    int static_eval = evaluate(state);

    // 2. Static Null Move Pruning (Reverse Futility Pruning)
    if (depth <= 3 && !in_check && !pv_node && !queen_sacced) {
        int margin = 120 * depth;
        if (static_eval - margin >= beta) {
            return static_eval - margin; // Fail high early
        }
    }

    // 3. Null Move Pruning (Deep search bypass heuristic)
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

    // 4. Futility Pruning
    bool futility_pruning_active = false;
    if (depth == 1 && !in_check && !pv_node && !queen_sacced) {
        if (static_eval + 150 < alpha) {
            futility_pruning_active = true;
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

        // Pruning logic: If queen is sacrificed, completely drop quiet choices outside the top 10 moves from thinking
        if (queen_sacced && legal_moves >= 10) {
            break; 
        }

        bool is_quiet = (state.board[m.to] == EMPTY && m.promoted == 0);

        // Skip quiet moves under futility constraints
        if (futility_pruning_active && is_quiet && legal_moves > 0) {
            continue;
        }

        BoardState next;
        if (!make_move(state, next, m)) continue;

        legal_moves++;
        Move temp_move = {0, 0, 0, 0};
        int score;

        // 5. Principal Variation Search (PVS) with Late Move Reduction (LMR)
        if (legal_moves == 1) {
            score = -search(next, depth - 1, ply + 1, -beta, -alpha, temp_move, {0, 0, 0, 0});
        } else {
            // Apply Late Move Reduction
            int r = 0;
            if (depth >= 3 && legal_moves > 4 && !in_check && is_quiet) {
                r = 1 + depth / 6 + legal_moves / 12;
                if (pv_node) r--; // Reduce less in PV nodes
                if (r < 0) r = 0;
            }

            if (r > 0) {
                score = -search(next, depth - 1 - r, ply + 1, -alpha - 1, -alpha, temp_move, {0, 0, 0, 0});
                if (score > alpha && score < beta) {
                    // Re-search at full depth
                    score = -search(next, depth - 1, ply + 1, -beta, -alpha, temp_move, {0, 0, 0, 0});
                }
            } else {
                score = -search(next, depth - 1, ply + 1, -alpha - 1, -alpha, temp_move, {0, 0, 0, 0});
            }

            // Re-search full window if PVS null window failed high
            if (score > alpha && score < beta) {
                score = -search(next, depth - 1, ply + 1, -beta, -alpha, temp_move, {0, 0, 0, 0});
            }
        }

        if (score > best_score) {
            best_score = score;
            local_best_move = m;
        }

        // Beta cutoff found
        if (score >= beta) {
            if (is_quiet) {
                store_killer(m, ply);
                // Reward history score
                history_moves[state.board[m.from]][m.to] += depth * depth;
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

    clear_history();

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

    int previous_score = 0;
    int alpha = -1000000;
    int beta = 1000000;

    for (int depth = 1; depth <= 12; ++depth) {
        Move current_best_move = {0, 0, 0, 0};
        int score = 0;

        // 6. Aspiration Windows (limits search bounds dynamically based on previous search results)
        if (depth >= 5) {
            int delta = 25;
            alpha = previous_score - delta;
            beta = previous_score + delta;

            while (true) {
                if (alpha < -25000) alpha = -1000000;
                if (beta > 25000) beta = 1000000;

                score = search(state, depth, 0, alpha, beta, current_best_move, last_completed_best_move);

                if (search_stopped) break;

                if (score <= alpha) {
                    alpha -= delta;
                    delta *= 2;
                } else if (score >= beta) {
                    beta += delta;
                    delta *= 2;
                } else {
                    break;
                }
            }
        } else {
            score = search(state, depth, 0, -1000000, 1000000, current_best_move, last_completed_best_move);
        }

        if (search_stopped) break;

        previous_score = score;
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

    uci_moves_played.clear(); // Restart book tracking for the session

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
                        uci_moves_played.push_back(move_str); // Log move into book path
                        break;
                    }
                }
            }
        }
    }
}

// Parse 'go' commands and allocate search time budget
void parse_go(const BoardState& state, const std::string& cmd) {
    // 1. Probe the opening book database
    if (opening_book.count(uci_moves_played) > 0) {
        const auto& book_moves = opening_book[uci_moves_played];
        if (!book_moves.empty()) {
            static std::mt19937 rng(static_cast<unsigned>(std::chrono::system_clock::now().time_since_epoch().count()));
            std::uniform_int_distribution<size_t> dist(0, book_moves.size() - 1);
            std::string chosen_uci = book_moves[dist(rng)];

            // Verify chosen move is legal before playing
            MoveList list;
            generate_moves(state, list);
            bool found_legal = false;
            for (int i = 0; i < list.count; ++i) {
                Move m = list.moves[i];
                std::string current_m_str = square_to_uci(m.from) + square_to_uci(m.to);
                if (m.promoted != 0) {
                    current_m_str += piece_to_promotion_char(m.promoted);
                }
                if (current_m_str == chosen_uci) {
                    BoardState next;
                    if (make_move(state, next, m)) {
                        found_legal = true;
                        break;
                    }
                }
            }

            if (found_legal) {
                std::cout << "info string Playing book move: " << chosen_uci << std::endl;
                std::cout << "bestmove " << chosen_uci << std::endl;
                return; // Play immediately, skip search budget execution
            }
        }
    }

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
    load_opening_book(); // Parses the comprehensive opening text database on startup

    BoardState state;
    load_fen(state, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");

    std::string line;
    while (std::getline(std::cin, line)) {
        if (line.empty()) continue;
        std::stringstream ss(line);
        std::string cmd;
        ss >> cmd;

        if (cmd == "uci") {
            std::cout << "id name IM_Engine_3000+" << std::endl;
            std::cout << "id author by: iain gaines 🇺🇸" << std::endl;
            std::cout << "uciok" << std::endl;
        } else if (cmd == "isready") {
            std::cout << "readyok" << std::endl;
        } else if (cmd == "ucinewgame") {
            clear_tt();
            uci_moves_played.clear();
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
