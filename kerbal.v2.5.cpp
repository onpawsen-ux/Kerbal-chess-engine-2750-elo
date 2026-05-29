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
#include <iomanip>
#include <cmath>
#include <memory>
#include <array>
#include <cstdint> // Added for uint64_t definition

#ifdef _WIN32
#include <windows.h>
#include <conio.h>
#else
#include <unistd.h>
#include <sys/select.h>
#endif

// ============================================================================
// BASIC TYPES, CONSTANTS AND REPS
// ============================================================================

enum Squares {
    A1 = 0x00, B1, C1, D1, E1, F1, G1, H1,
    A2 = 0x10, B2, C2, D2, E2, F2, G2, H2,
    A3 = 0x20, B3, C3, D3, E3, F3, G3, H3,
    A4 = 0x30, B4, C4, D4, E4, F4, G4, H4,
    A5 = 0x40, B5, C5, D5, E5, F5, G5, H5,
    A6 = 0x50, B6, C6, D6, E6, F6, G6, H6,
    A7 = 0x60, B7, C7, D7, E7, F7, G7, H7,
    A8 = 0x70, B8, C8, D8, E8, F8, G8, H8,
    NO_SQ = -1
};

enum Pieces { EMPTY, WP, WN, WB, WR, WQ, WK, BP, BN, BB, BR, BQ, BK };
enum Colors { WHITE, BLACK, BOTH };
enum TTFlags { TT_EXACT, TT_ALPHA, TT_BETA };

enum Castling {
    WK_CASTLE = 1,
    WQ_CASTLE = 2,
    BK_CASTLE = 4,
    BQ_CASTLE = 8
};

// Structures for moves
struct Move {
    int from;
    int to;
    int promoted;
    int score;

    bool operator==(const Move& other) const {
        return from == other.from && to == other.to && promoted == other.promoted;
    }
    bool operator!=(const Move& other) const {
        return !(*this == other);
    }
};

struct MoveList {
    Move moves[256];
    int count = 0;
    inline void push(const Move& m) {
        if (count < 256) {
            moves[count++] = m;
        }
    }
};

struct UndoInfo {
    int castling;
    int enpassant;
    int halfmove_clock;
    int captured_piece;
    uint64_t hash;
};

// Encapsulates the double-linked piece list tracking board
struct Position {
    int board[128];
    int side;
    int castling;
    int enpassant;
    int halfmove_clock;
    int fullmove_number;
    uint64_t hash;

    // Fast piece iteration lists
    int piece_list[13][16];
    int piece_count[13];
    int piece_index[128];
};

// Precalculation tables for speed
namespace Precalc {
    int squares_between[128][128];
    int ray_directions[128][128];
    int manhattan_distance[128][128];
    int chebyshev_distance[128][128];
    int king_safety_zones[2][128][9]; // [color][sq][index]
    int king_safety_zone_counts[2][128];
}

// Global Move ordering score values
const int knight_offsets[] = {-33, -31, -18, -14, 14, 18, 31, 33};
const int bishop_offsets[] = {-17, -15, 15, 17};
const int rook_offsets[] = {-16, -1, 1, 16};
const int king_offsets[] = {-17, -16, -15, -1, 1, 15, 16, 17};

// Evaluation weights and phases
const int mg_value[] = { 0, 82, 337, 365, 477, 1025, 0, 82, 337, 365, 477, 1025, 0 };
const int eg_value[] = { 0, 94, 281, 297, 512,  936, 0, 94, 281, 297, 512,  936, 0 };
const int see_values[] = { 0, 100, 325, 330, 500, 900, 20000, 100, 325, 330, 500, 900, 20000 };

// Attacking values for King danger
const int attacker_weights[] = { 0, 0, 2, 2, 3, 5, 0, 0, 2, 2, 3, 5, 0 };

// PST Matrices (flipped internally)
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

// ============================================================================
// SYSTEM GLOBALS
// ============================================================================

uint64_t repetition_history[2048];
int repetition_count = 0;

std::chrono::time_point<std::chrono::steady_clock> search_start;
double search_time_limit_ms = 1000.0;
bool search_stopped = false;
int nodes_searched = 0;
int current_max_depth = 64;

uint64_t piece_keys[13][128];
uint64_t side_key;
uint64_t castle_keys[16];
uint64_t ep_keys[128];

// Move ordering structures
Move killer_moves[2][128];
int history_moves[13][128];
Move counter_moves[13][128];
int lmr_table[64][256];

std::vector<std::string> uci_moves_played;
std::map<std::vector<std::string>, std::vector<std::string>> opening_book;

// ============================================================================
// TRANSPOSITION TABLE & BUCKETS
// ============================================================================

// Defined the missing TTEntry struct
struct TTEntry {
    uint64_t key;
    int depth;
    int flag;
    int value;
    Move best_move;
    int age;
};

struct TTBucket {
    TTEntry entries[4]; // 4-way associative buckets
};

const int TT_SIZE = 1 << 19; // ~500k buckets (each has 4 entries) -> 2M entries
TTBucket* transposition_table = nullptr;
int tt_current_age = 0;

void init_tt() {
    if (transposition_table) delete[] transposition_table;
    transposition_table = new TTBucket[TT_SIZE]();
}

void clear_tt() {
    if (transposition_table) {
        std::memset(transposition_table, 0, sizeof(TTBucket) * TT_SIZE);
    }
    tt_current_age = 0;
}

// ============================================================================
// PAWN CACHE TABLE
// ============================================================================

struct PawnEntry {
    uint64_t key;
    int score_mg;
    int score_eg;
};

const int PAWN_TABLE_SIZE = 1 << 16; // 64k entries
PawnEntry* pawn_table = nullptr;

void init_pawn_table() {
    if (pawn_table) delete[] pawn_table;
    pawn_table = new PawnEntry[PAWN_TABLE_SIZE]();
}

void clear_pawn_table() {
    if (pawn_table) {
        std::memset(pawn_table, 0, sizeof(PawnEntry) * PAWN_TABLE_SIZE);
    }
}

// ============================================================================
// REPRESENTATION INLINES
// ============================================================================

inline int get_color(int piece) {
    if (piece == EMPTY) return BOTH;
    return (piece <= WK) ? WHITE : BLACK;
}

inline int get_piece_type(int piece) {
    if (piece == EMPTY) return EMPTY;
    return (piece <= WK) ? piece : piece - 6;
}

inline int square_to_64(int sq) {
    return (sq >> 4) * 8 + (sq & 7);
}

inline int square_from_64(int idx) {
    return ((idx / 8) << 4) + (idx % 8);
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

// ============================================================================
// PRECALCULATIONS INITIALIZATION
// ============================================================================

void init_precalculations() {
    std::memset(Precalc::squares_between, 0, sizeof(Precalc::squares_between));
    std::memset(Precalc::ray_directions, 0, sizeof(Precalc::ray_directions));

    for (int sq1 = 0; sq1 < 128; ++sq1) {
        if (sq1 & 0x88) continue;
        int r1 = sq1 >> 4;
        int f1 = sq1 & 7;

        for (int sq2 = 0; sq2 < 128; ++sq2) {
            if (sq2 & 0x88) continue;
            int r2 = sq2 >> 4;
            int f2 = sq2 & 7;

            // Distances
            Precalc::manhattan_distance[sq1][sq2] = std::abs(r1 - r2) + std::abs(f1 - f2);
            Precalc::chebyshev_distance[sq1][sq2] = std::max(std::abs(r1 - r2), std::abs(f1 - f2));

            // Ray & Line precalculations
            if (sq1 == sq2) continue;

            int dr = r2 - r1;
            int df = f2 - f1;

            int step_r = (dr > 0) ? 1 : ((dr < 0) ? -1 : 0);
            int step_f = (df > 0) ? 1 : ((df < 0) ? -1 : 0);

            // Verify straight directional alignment
            bool straight_aligned = false;
            if (dr == 0 || df == 0 || std::abs(dr) == std::abs(df)) {
                straight_aligned = true;
            }

            if (straight_aligned) {
                int direction_step = (step_r << 4) + step_f;
                Precalc::ray_directions[sq1][sq2] = direction_step;

                // Trace path between them
                int trace = sq1 + direction_step;
                int count = 0;
                while (trace != sq2 && count < 8) {
                    Precalc::squares_between[sq1][sq2] |= (1 << count); // Store step index
                    trace += direction_step;
                    count++;
                }
            }
        }
    }

    // King safety zone calculations
    for (int color = 0; color < 2; ++color) {
        for (int sq = 0; sq < 128; ++sq) {
            if (sq & 0x88) continue;
            int count = 0;
            // King's current square
            Precalc::king_safety_zones[color][sq][count++] = sq;

            // Surrounding 8 squares plus forward adjacents
            for (int offset : king_offsets) {
                int target = sq + offset;
                if (!(target & 0x88)) {
                    Precalc::king_safety_zones[color][sq][count++] = target;
                }
            }
            Precalc::king_safety_zone_counts[color][sq] = count;
        }
    }
}

// ============================================================================
// DOUBLE-LINKED PIECE LIST CONTROL
// ============================================================================

void add_piece_to_lists(Position& pos, int sq, int piece) {
    pos.board[sq] = piece;
    int count = pos.piece_count[piece];
    pos.piece_list[piece][count] = sq;
    pos.piece_index[sq] = count;
    pos.piece_count[piece]++;
}

void remove_piece_from_lists(Position& pos, int sq, int piece) {
    int index_to_remove = pos.piece_index[sq];
    int last_index = pos.piece_count[piece] - 1;
    int last_sq = pos.piece_list[piece][last_index];

    pos.piece_list[piece][index_to_remove] = last_sq;
    pos.piece_index[last_sq] = index_to_remove;

    pos.piece_count[piece]--;
    pos.board[sq] = EMPTY;
    pos.piece_index[sq] = -1;
}

void move_piece_in_lists(Position& pos, int from, int to, int piece) {
    int idx = pos.piece_index[from];
    pos.piece_list[piece][idx] = to;
    pos.piece_index[to] = idx;
    pos.board[to] = piece;
    pos.board[from] = EMPTY;
    pos.piece_index[from] = -1;
}

// ============================================================================
// SEED-REPRODUCIBLE RANDOM GENERATOR & ZOBRIST HASHES
// ============================================================================

struct PRNG {
    uint64_t state;
    uint64_t next() {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        return state * 2685821657736338717ULL;
    }
};

void init_zobrist() {
    PRNG prng{10398012ULL};
    for (int p = 0; p < 13; ++p) {
        for (int sq = 0; sq < 128; ++sq) {
            piece_keys[p][sq] = prng.next();
        }
    }
    side_key = prng.next();
    for (int i = 0; i < 16; ++i) {
        castle_keys[i] = prng.next();
    }
    for (int i = 0; i < 128; ++i) {
        ep_keys[i] = prng.next();
    }
}

uint64_t generate_hash(const Position& pos) {
    uint64_t h = 0;
    for (int sq = 0; sq < 128; ++sq) {
        if (sq & 0x88) continue;
        int piece = pos.board[sq];
        if (piece != EMPTY) {
            h ^= piece_keys[piece][sq];
        }
    }
    if (pos.side == BLACK) h ^= side_key;
    h ^= castle_keys[pos.castling];
    if (pos.enpassant != -1) {
        h ^= ep_keys[pos.enpassant];
    }
    return h;
}

// ============================================================================
// TRANSPOSITION TABLE BUCKET-BASED FUNCTIONS
// ============================================================================

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

bool tt_probe(uint64_t key, int depth, int ply, int alpha, int beta, int& score, Move& best_move) {
    TTBucket& bucket = transposition_table[key % TT_SIZE];
    for (int i = 0; i < 4; ++i) {
        TTEntry& entry = bucket.entries[i];
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
    }
    return false;
}

void tt_store(uint64_t key, int depth, int ply, int flag, int score, const Move& best_move) {
    TTBucket& bucket = transposition_table[key % TT_SIZE];

    int target_idx = -1;
    int worst_depth = 999;

    // Look for key match or empty entry
    for (int i = 0; i < 4; ++i) {
        if (bucket.entries[i].key == key) {
            target_idx = i;
            break;
        }
        if (bucket.entries[i].key == 0) {
            target_idx = i;
            break;
        }
    }

    // Two-tier replacement if all entries are occupied
    if (target_idx == -1) {
        for (int i = 0; i < 4; ++i) {
            if (bucket.entries[i].age != tt_current_age) {
                target_idx = i; // Discard entries from a different search age
                break;
            }
            if (bucket.entries[i].depth < worst_depth) {
                worst_depth = bucket.entries[i].depth;
                target_idx = i; // Fallback to shallowest entry
            }
        }
    }

    if (target_idx != -1) {
        TTEntry& entry = bucket.entries[target_idx];
        entry.key = key;
        entry.depth = depth;
        entry.flag = flag;
        entry.value = score_to_tt(score, ply);
        entry.best_move = best_move;
        entry.age = tt_current_age;
    }
}

// ============================================================================
// ATTACK & LEGALITY DETECTORS
// ============================================================================

bool is_square_attacked(const Position& pos, int sq, int attacker_side) {
    if (sq & 0x88) return false;

    // 1. Knights
    int enemy_knight = (attacker_side == WHITE) ? WN : BN;
    for (int offset : knight_offsets) {
        int target = sq + offset;
        if (!(target & 0x88) && pos.board[target] == enemy_knight) return true;
    }

    // 2. Pawns
    if (attacker_side == WHITE) {
        int left = sq - 17, right = sq - 15;
        if (!(left & 0x88) && pos.board[left] == WP) return true;
        if (!(right & 0x88) && pos.board[right] == WP) return true;
    } else {
        int left = sq + 17, right = sq + 15;
        if (!(left & 0x88) && pos.board[left] == BP) return true;
        if (!(right & 0x88) && pos.board[right] == BP) return true;
    }

    // 3. Bishops / Queens
    int enemy_bishop = (attacker_side == WHITE) ? WB : BB;
    int enemy_queen = (attacker_side == WHITE) ? WQ : BQ;
    for (int offset : bishop_offsets) {
        int target = sq + offset;
        while (!(target & 0x88)) {
            int piece = pos.board[target];
            if (piece != EMPTY) {
                if (piece == enemy_bishop || piece == enemy_queen) return true;
                break;
            }
            target += offset;
        }
    }

    // 4. Rooks / Queens
    int enemy_rook = (attacker_side == WHITE) ? WR : BR;
    for (int offset : rook_offsets) {
        int target = sq + offset;
        while (!(target & 0x88)) {
            int piece = pos.board[target];
            if (piece != EMPTY) {
                if (piece == enemy_rook || piece == enemy_queen) return true;
                break;
            }
            target += offset;
        }
    }

    // 5. Kings
    int enemy_king = (attacker_side == WHITE) ? WK : BK;
    for (int offset : king_offsets) {
        int target = sq + offset;
        if (!(target & 0x88) && pos.board[target] == enemy_king) return true;
    }

    return false;
}

bool is_in_check(const Position& pos) {
    int us = pos.side;
    int them = (us == WHITE) ? BLACK : WHITE;
    int king_piece = (us == WHITE) ? WK : BK;

    if (pos.piece_count[king_piece] == 0) return false;
    int king_sq = pos.piece_list[king_piece][0];
    return is_square_attacked(pos, king_sq, them);
}

// ============================================================================
// STATIC EXCHANGE EVALUATION (SEE)
// ============================================================================

int get_smallest_attacker(const Position& pos, int sq, int side, int& attacker_sq) {
    int start_pawn = (side == WHITE) ? WP : BP;
    int start_knight = (side == WHITE) ? WN : BN;
    int start_bishop = (side == WHITE) ? WB : BB;
    int start_rook = (side == WHITE) ? WR : BR;
    int start_queen = (side == WHITE) ? WQ : BQ;
    int start_king = (side == WHITE) ? WK : BK;

    // 1. Pawn
    if (side == WHITE) {
        int left = sq - 17, right = sq - 15;
        if (!(left & 0x88) && pos.board[left] == start_pawn) { attacker_sq = left; return start_pawn; }
        if (!(right & 0x88) && pos.board[right] == start_pawn) { attacker_sq = right; return start_pawn; }
    } else {
        int left = sq + 17, right = sq + 15;
        if (!(left & 0x88) && pos.board[left] == start_pawn) { attacker_sq = left; return start_pawn; }
        if (!(right & 0x88) && pos.board[right] == start_pawn) { attacker_sq = right; return start_pawn; }
    }

    // 2. Knight
    for (int offset : knight_offsets) {
        int target = sq + offset;
        if (!(target & 0x88) && pos.board[target] == start_knight) {
            attacker_sq = target;
            return start_knight;
        }
    }

    // 3. Bishop
    for (int offset : bishop_offsets) {
        int target = sq + offset;
        while (!(target & 0x88)) {
            int piece = pos.board[target];
            if (piece != EMPTY) {
                if (piece == start_bishop) { attacker_sq = target; return start_bishop; }
                break;
            }
            target += offset;
        }
    }

    // 4. Rook
    for (int offset : rook_offsets) {
        int target = sq + offset;
        while (!(target & 0x88)) {
            int piece = pos.board[target];
            if (piece != EMPTY) {
                if (piece == start_rook) { attacker_sq = target; return start_rook; }
                break;
            }
            target += offset;
        }
    }

    // 5. Queen
    for (int offset : king_offsets) {
        int target = sq + offset;
        while (!(target & 0x88)) {
            int piece = pos.board[target];
            if (piece != EMPTY) {
                if (piece == start_queen) { attacker_sq = target; return start_queen; }
                break;
            }
            target += offset;
        }
    }

    // 6. King
    for (int offset : king_offsets) {
        int target = sq + offset;
        if (!(target & 0x88) && pos.board[target] == start_king) {
            attacker_sq = target;
            return start_king;
        }
    }

    return EMPTY;
}

int see(Position& pos, int from, int to) {
    int value_stack[32];
    int depth = 0;

    int victim = pos.board[to];
    int attacker = pos.board[from];

    value_stack[0] = see_values[victim];
    int current_side = pos.side;

    int current_sq = from;
    int current_piece = attacker;

    int temp_board[128];
    std::memcpy(temp_board, pos.board, sizeof(pos.board));

    pos.board[to] = current_piece;
    pos.board[current_sq] = EMPTY;

    int side = (current_side == WHITE) ? BLACK : WHITE;

    while (true) {
        int next_attacker_sq = -1;
        int next_attacker = get_smallest_attacker(pos, to, side, next_attacker_sq);

        // Added depth limit check to prevent stack overflow
        if (next_attacker == EMPTY || depth >= 31) break;

        depth++;
        value_stack[depth] = see_values[pos.board[to]] - value_stack[depth - 1];

        // Handle illegal King checks in calculation
        if (next_attacker == WK || next_attacker == BK) {
            if (is_square_attacked(pos, to, (side == WHITE) ? BLACK : WHITE)) {
                depth--;
                break;
            }
        }

        pos.board[to] = next_attacker;
        pos.board[next_attacker_sq] = EMPTY;

        side = (side == WHITE) ? BLACK : WHITE;
    }

    while (depth > 0) {
        value_stack[depth - 1] = see_values[pos.board[to]] - std::max(0, value_stack[depth]);
        depth--;
    }

    std::memcpy(pos.board, temp_board, sizeof(pos.board));

    return value_stack[0];
}

// ============================================================================
// MOVE GENERATOR
// ============================================================================

void generate_moves(const Position& pos, MoveList& list) {
    int us = pos.side;
    int them = (us == WHITE) ? BLACK : WHITE;

    // 1. Pawn moves
    int pawn = (us == WHITE) ? WP : BP;
    for (int i = 0; i < pos.piece_count[pawn]; ++i) {
        int sq = pos.piece_list[pawn][i];
        if (us == WHITE) {
            int to = sq + 16;
            if (!(to & 0x88) && pos.board[to] == EMPTY) {
                if ((to >> 4) == 7) {
                    list.push({sq, to, WQ, 0});
                    list.push({sq, to, WR, 0});
                    list.push({sq, to, WB, 0});
                    list.push({sq, to, WN, 0});
                } else {
                    list.push({sq, to, 0, 0});
                    int to2 = sq + 32;
                    if ((sq >> 4) == 1 && pos.board[to2] == EMPTY) {
                        list.push({sq, to2, 0, 0});
                    }
                }
            }
            int caps[] = {sq + 15, sq + 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (pos.board[to_cap] != EMPTY && get_color(pos.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 7) {
                            list.push({sq, to_cap, WQ, 0});
                            list.push({sq, to_cap, WR, 0});
                            list.push({sq, to_cap, WB, 0});
                            list.push({sq, to_cap, WN, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == pos.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        } else {
            int to = sq - 16;
            if (!(to & 0x88) && pos.board[to] == EMPTY) {
                if ((to >> 4) == 0) {
                    list.push({sq, to, BQ, 0});
                    list.push({sq, to, BR, 0});
                    list.push({sq, to, BB, 0});
                    list.push({sq, to, BN, 0});
                } else {
                    list.push({sq, to, 0, 0});
                    int to2 = sq - 32;
                    if ((sq >> 4) == 6 && pos.board[to2] == EMPTY) {
                        list.push({sq, to2, 0, 0});
                    }
                }
            }
            int caps[] = {sq - 15, sq - 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (pos.board[to_cap] != EMPTY && get_color(pos.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 0) {
                            list.push({sq, to_cap, BQ, 0});
                            list.push({sq, to_cap, BR, 0});
                            list.push({sq, to_cap, BB, 0});
                            list.push({sq, to_cap, BN, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == pos.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        }
    }

    // 2. Knights
    int knight = (us == WHITE) ? WN : BN;
    for (int i = 0; i < pos.piece_count[knight]; ++i) {
        int sq = pos.piece_list[knight][i];
        for (int offset : knight_offsets) {
            int to = sq + offset;
            if (!(to & 0x88)) {
                if (pos.board[to] == EMPTY || get_color(pos.board[to]) == them) {
                    list.push({sq, to, 0, 0});
                }
            }
        }
    }

    // 3. Bishops
    int bishop = (us == WHITE) ? WB : BB;
    for (int i = 0; i < pos.piece_count[bishop]; ++i) {
        int sq = pos.piece_list[bishop][i];
        for (int offset : bishop_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target == EMPTY) {
                    list.push({sq, to, 0, 0});
                } else {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
    }

    // 4. Rooks
    int rook = (us == WHITE) ? WR : BR;
    for (int i = 0; i < pos.piece_count[rook]; ++i) {
        int sq = pos.piece_list[rook][i];
        for (int offset : rook_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target == EMPTY) {
                    list.push({sq, to, 0, 0});
                } else {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
    }

    // 5. Queens
    int queen = (us == WHITE) ? WQ : BQ;
    for (int i = 0; i < pos.piece_count[queen]; ++i) {
        int sq = pos.piece_list[queen][i];
        for (int offset : bishop_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target == EMPTY) {
                    list.push({sq, to, 0, 0});
                } else {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
        for (int offset : rook_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target == EMPTY) {
                    list.push({sq, to, 0, 0});
                } else {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
    }

    // 6. King & Castling
    int king = (us == WHITE) ? WK : BK;
    if (pos.piece_count[king] > 0) {
        int sq = pos.piece_list[king][0];
        for (int offset : king_offsets) {
            int to = sq + offset;
            if (!(to & 0x88)) {
                if (pos.board[to] == EMPTY || get_color(pos.board[to]) == them) {
                    list.push({sq, to, 0, 0});
                }
            }
        }

        // WK/WQ Castling
        if (us == WHITE && sq == E1) {
            if ((pos.castling & WK_CASTLE) && pos.board[F1] == EMPTY && pos.board[G1] == EMPTY) {
                if (!is_square_attacked(pos, E1, BLACK) &&
                    !is_square_attacked(pos, F1, BLACK) &&
                    !is_square_attacked(pos, G1, BLACK)) {
                    list.push({E1, G1, 0, 0});
                }
            }
            if ((pos.castling & WQ_CASTLE) && pos.board[D1] == EMPTY && pos.board[C1] == EMPTY && pos.board[B1] == EMPTY) {
                if (!is_square_attacked(pos, E1, BLACK) &&
                    !is_square_attacked(pos, D1, BLACK) &&
                    !is_square_attacked(pos, C1, BLACK)) {
                    list.push({E1, C1, 0, 0});
                }
            }
        } else if (us == BLACK && sq == E8) {
            if ((pos.castling & BK_CASTLE) && pos.board[F8] == EMPTY && pos.board[G8] == EMPTY) {
                if (!is_square_attacked(pos, E8, WHITE) &&
                    !is_square_attacked(pos, F8, WHITE) &&
                    !is_square_attacked(pos, G8, WHITE)) {
                    list.push({E8, G8, 0, 0});
                }
            }
            if ((pos.castling & BQ_CASTLE) && pos.board[D8] == EMPTY && pos.board[C8] == EMPTY && pos.board[B8] == EMPTY) {
                if (!is_square_attacked(pos, E8, WHITE) &&
                    !is_square_attacked(pos, D8, WHITE) &&
                    !is_square_attacked(pos, C8, WHITE)) {
                    list.push({E8, C8, 0, 0});
                }
            }
        }
    }
}

void generate_captures(const Position& pos, MoveList& list) {
    int us = pos.side;
    int them = (us == WHITE) ? BLACK : WHITE;

    // Pawns
    int pawn = (us == WHITE) ? WP : BP;
    for (int i = 0; i < pos.piece_count[pawn]; ++i) {
        int sq = pos.piece_list[pawn][i];
        if (us == WHITE) {
            int caps[] = {sq + 15, sq + 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (pos.board[to_cap] != EMPTY && get_color(pos.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 7) {
                            list.push({sq, to_cap, WQ, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == pos.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        } else {
            int caps[] = {sq - 15, sq - 17};
            for (int to_cap : caps) {
                if (!(to_cap & 0x88)) {
                    if (pos.board[to_cap] != EMPTY && get_color(pos.board[to_cap]) == them) {
                        if ((to_cap >> 4) == 0) {
                            list.push({sq, to_cap, BQ, 0});
                        } else {
                            list.push({sq, to_cap, 0, 0});
                        }
                    } else if (to_cap == pos.enpassant) {
                        list.push({sq, to_cap, 0, 0});
                    }
                }
            }
        }
    }

    // Knights
    int knight = (us == WHITE) ? WN : BN;
    for (int i = 0; i < pos.piece_count[knight]; ++i) {
        int sq = pos.piece_list[knight][i];
        for (int offset : knight_offsets) {
            int to = sq + offset;
            if (!(to & 0x88) && pos.board[to] != EMPTY && get_color(pos.board[to]) == them) {
                list.push({sq, to, 0, 0});
            }
        }
    }

    // Bishops
    int bishop = (us == WHITE) ? WB : BB;
    for (int i = 0; i < pos.piece_count[bishop]; ++i) {
        int sq = pos.piece_list[bishop][i];
        for (int offset : bishop_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target != EMPTY) {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
    }

    // Rooks
    int rook = (us == WHITE) ? WR : BR;
    for (int i = 0; i < pos.piece_count[rook]; ++i) {
        int sq = pos.piece_list[rook][i];
        for (int offset : rook_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target != EMPTY) {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
    }

    // Queens
    int queen = (us == WHITE) ? WQ : BQ;
    for (int i = 0; i < pos.piece_count[queen]; ++i) {
        int sq = pos.piece_list[queen][i];
        for (int offset : bishop_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target != EMPTY) {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
        for (int offset : rook_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                int target = pos.board[to];
                if (target != EMPTY) {
                    if (get_color(target) == them) list.push({sq, to, 0, 0});
                    break;
                }
                to += offset;
            }
        }
    }

    // King
    int king = (us == WHITE) ? WK : BK;
    if (pos.piece_count[king] > 0) {
        int sq = pos.piece_list[king][0];
        for (int offset : king_offsets) {
            int to = sq + offset;
            if (!(to & 0x88) && pos.board[to] != EMPTY && get_color(pos.board[to]) == them) {
                list.push({sq, to, 0, 0});
            }
        }
    }
}

// ============================================================================
// STATE MACHINE ACTIONS (MAKE & UNMAKE MOVES)
// ============================================================================

bool make_move(Position& pos, const Move& m, UndoInfo& undo) {
    int from = m.from;
    int to = m.to;

    // Safety checks for indices
    if (from < 0 || from >= 128 || (from & 0x88) || to < 0 || to >= 128 || (to & 0x88)) {
        return false;
    }

    int piece = pos.board[from];
    int victim = pos.board[to];

    undo.castling = pos.castling;
    undo.enpassant = pos.enpassant;
    undo.halfmove_clock = pos.halfmove_clock;
    undo.captured_piece = victim;
    undo.hash = pos.hash;

    pos.hash ^= piece_keys[piece][from];

    if (pos.enpassant != -1) pos.hash ^= ep_keys[pos.enpassant];
    pos.hash ^= castle_keys[pos.castling];

    // En Passant captures
    if ((piece == WP || piece == BP) && to == pos.enpassant) {
        int ep_pawn_sq = (piece == WP) ? (to - 16) : (to + 16);
        undo.captured_piece = pos.board[ep_pawn_sq];
        pos.hash ^= piece_keys[undo.captured_piece][ep_pawn_sq];
        remove_piece_from_lists(pos, ep_pawn_sq, undo.captured_piece);
    } 
    // Standard captures
    else if (victim != EMPTY) {
        pos.hash ^= piece_keys[victim][to];
        remove_piece_from_lists(pos, to, victim);
    }

    // Castling updates
    if (piece == WK && from == E1) {
        if (to == G1) {
            pos.hash ^= piece_keys[WR][H1] ^ piece_keys[WR][F1];
            move_piece_in_lists(pos, H1, F1, WR);
        } else if (to == C1) {
            pos.hash ^= piece_keys[WR][A1] ^ piece_keys[WR][D1];
            move_piece_in_lists(pos, A1, D1, WR);
        }
    } else if (piece == BK && from == E8) {
        if (to == G8) {
            pos.hash ^= piece_keys[BR][H8] ^ piece_keys[BR][F8];
            move_piece_in_lists(pos, H8, F8, BR);
        } else if (to == C8) {
            pos.hash ^= piece_keys[BR][A8] ^ piece_keys[BR][D8];
            move_piece_in_lists(pos, A8, D8, BR);
        }
    }

    // Adjust castling mask
    if (piece == WK) pos.castling &= ~3;
    if (piece == BK) pos.castling &= ~12;
    if (from == A1 || to == A1) pos.castling &= ~2;
    if (from == H1 || to == H1) pos.castling &= ~1;
    if (from == A8 || to == A8) pos.castling &= ~8;
    if (from == H8 || to == H8) pos.castling &= ~4;

    move_piece_in_lists(pos, from, to, piece);

    // Apply promotion
    if (m.promoted != EMPTY) {
        remove_piece_from_lists(pos, to, piece);
        add_piece_to_lists(pos, to, m.promoted);
        pos.hash ^= piece_keys[m.promoted][to];
    } else {
        pos.hash ^= piece_keys[piece][to];
    }

    // En Passant generation
    pos.enpassant = -1;
    if (piece == WP && (to - from == 32)) {
        pos.enpassant = from + 16;
    } else if (piece == BP && (from - to == 32)) {
        pos.enpassant = from - 16;
    }

    if (pos.enpassant != -1) pos.hash ^= ep_keys[pos.enpassant];
    pos.hash ^= castle_keys[pos.castling];

    if (piece == WP || piece == BP || victim != EMPTY) {
        pos.halfmove_clock = 0;
    } else {
        pos.halfmove_clock++;
    }

    int us = pos.side;
    pos.side = (us == WHITE) ? BLACK : WHITE;
    pos.hash ^= side_key;

    if (pos.side == WHITE) pos.fullmove_number++;

    // Safety check: King cannot remain in check after move
    int king_piece = (us == WHITE) ? WK : BK;
    if (pos.piece_count[king_piece] > 0) {
        int king_sq = pos.piece_list[king_piece][0];
        if (is_square_attacked(pos, king_sq, pos.side)) {
            // Restore illegal move
            pos.side = us;
            pos.hash ^= side_key;
            if (pos.side == WHITE) pos.fullmove_number--;

            if (m.promoted != EMPTY) {
                remove_piece_from_lists(pos, to, m.promoted);
                add_piece_to_lists(pos, to, piece);
            }
            move_piece_in_lists(pos, to, from, piece);

            if ((piece == WP || piece == BP) && to == undo.enpassant) {
                int ep_pawn_sq = (piece == WP) ? (to - 16) : (to + 16);
                add_piece_to_lists(pos, ep_pawn_sq, undo.captured_piece);
                pos.board[to] = EMPTY;
            } else if (victim != EMPTY) {
                add_piece_to_lists(pos, to, victim);
            }

            if (piece == WK && from == E1) {
                if (to == G1) move_piece_in_lists(pos, F1, H1, WR);
                else if (to == C1) move_piece_in_lists(pos, D1, A1, WR);
            } else if (piece == BK && from == E8) {
                if (to == G8) move_piece_in_lists(pos, F8, H8, BR);
                else if (to == C8) move_piece_in_lists(pos, D8, A8, BR);
            }

            pos.castling = undo.castling;
            pos.enpassant = undo.enpassant;
            pos.halfmove_clock = undo.halfmove_clock;
            pos.hash = undo.hash;
            return false;
        }
    }

    return true;
}

void unmake_move(Position& pos, const Move& m, const UndoInfo& undo) {
    int from = m.from;
    int to = m.to;
    int piece = pos.board[to];

    int us = (pos.side == WHITE) ? BLACK : WHITE;
    if (pos.side == WHITE) pos.fullmove_number--;

    pos.side = us;

    if (m.promoted != EMPTY) {
        remove_piece_from_lists(pos, to, m.promoted);
        add_piece_to_lists(pos, to, (us == WHITE) ? WP : BP);
        piece = pos.board[to];
    }

    move_piece_in_lists(pos, to, from, piece);

    if ((piece == WP || piece == BP) && to == undo.enpassant) {
        int ep_pawn_sq = (piece == WP) ? (to - 16) : (to + 16);
        add_piece_to_lists(pos, ep_pawn_sq, undo.captured_piece);
    } else if (undo.captured_piece != EMPTY) {
        add_piece_to_lists(pos, to, undo.captured_piece);
    }

    if (piece == WK && from == E1) {
        if (to == G1) move_piece_in_lists(pos, F1, H1, WR);
        else if (to == C1) move_piece_in_lists(pos, D1, A1, WR);
    } else if (piece == BK && from == E8) {
        if (to == G8) move_piece_in_lists(pos, F8, H8, BR);
        else if (to == C8) move_piece_in_lists(pos, D8, A8, BR);
    }

    pos.castling = undo.castling;
    pos.enpassant = undo.enpassant;
    pos.halfmove_clock = undo.halfmove_clock;
    pos.hash = undo.hash;
}

// ============================================================================
// DETAILED EVALUATION FUNCTION WITH CACHING
// ============================================================================

bool is_pawn_isolated(const Position& pos, int sq, int color) {
    int file = sq & 7;
    int target_pawn = (color == WHITE) ? WP : BP;
    for (int r = 0; r < 8; ++r) {
        if (file > 0 && pos.board[(r << 4) + file - 1] == target_pawn) return false;
        if (file < 7 && pos.board[(r << 4) + file + 1] == target_pawn) return false;
    }
    return true;
}

bool is_pawn_passed(const Position& pos, int sq, int color) {
    int file = sq & 7;
    int rank = sq >> 4;
    int enemy_pawn = (color == WHITE) ? BP : WP;
    if (color == WHITE) {
        for (int r = rank + 1; r < 8; ++r) {
            if (pos.board[(r << 4) + file] == enemy_pawn) return false;
            if (file > 0 && pos.board[(r << 4) + file - 1] == enemy_pawn) return false;
            if (file < 7 && pos.board[(r << 4) + file + 1] == enemy_pawn) return false;
        }
    } else {
        for (int r = rank - 1; r >= 0; --r) {
            if (pos.board[(r << 4) + file] == enemy_pawn) return false;
            if (file > 0 && pos.board[(r << 4) + file - 1] == enemy_pawn) return false;
            if (file < 7 && pos.board[(r << 4) + file + 1] == enemy_pawn) return false;
        }
    }
    return true;
}

bool is_pawn_doubled(const Position& pos, int sq, int color) {
    int file = sq & 7;
    int rank = sq >> 4;
    int pawn = (color == WHITE) ? WP : BP;
    for (int r = 0; r < 8; ++r) {
        if (r != rank && pos.board[(r << 4) + file] == pawn) return true;
    }
    return false;
}

// Advanced King danger safety checks
int evaluate_king_safety(const Position& pos, int king_sq, int color) {
    int penalty = 0;
    int enemy_color = (color == WHITE) ? BLACK : WHITE;

    // Check pawn shielding
    int rank = king_sq >> 4;
    int file = king_sq & 7;
    int friendly_pawn = (color == WHITE) ? WP : BP;
    int direction = (color == WHITE) ? 1 : -1;
    int shield_rank = rank + direction;

    if (shield_rank >= 0 && shield_rank < 8) {
        for (int f_offset = -1; f_offset <= 1; ++f_offset) {
            int check_file = file + f_offset;
            if (check_file >= 0 && check_file < 8) {
                int target_sq = (shield_rank << 4) + check_file;
                if (pos.board[target_sq] != friendly_pawn) {
                    penalty -= 15; // Shield missing penalty
                }
            }
        }
    }

    // Scaled Attacker Weights penalty based on virtual zone coverage
    int zone_attacks = 0;
    int attacker_weight_sum = 0;

    int zone_size = Precalc::king_safety_zone_counts[color][king_sq];
    for (int idx = 0; idx < zone_size; ++idx) {
        int zone_sq = Precalc::king_safety_zones[color][king_sq][idx];

        // Loop over enemy pieces to check attacks on this zone square
        for (int p_type = WP; p_type <= BK; ++p_type) {
            if (get_color(p_type) != enemy_color) continue;
            int count = pos.piece_count[p_type];
            for (int p_idx = 0; p_idx < count; ++p_idx) {
                int enemy_sq = pos.piece_list[p_type][p_idx];

                // Fast directional validation
                int ray = Precalc::ray_directions[enemy_sq][zone_sq];
                if (ray != 0 || Precalc::chebyshev_distance[enemy_sq][zone_sq] <= 2) {
                    zone_attacks++;
                    attacker_weight_sum += attacker_weights[p_type];
                }
            }
        }
    }

    if (zone_attacks > 0) {
        penalty -= (zone_attacks * attacker_weight_sum) / 3;
    }

    return penalty;
}

int evaluate_rook_files(const Position& pos, int sq, int color) {
    int score = 0;
    int file = sq & 7;
    bool friendly_pawn_present = false;
    bool enemy_pawn_present = false;
    int us_pawn = (color == WHITE) ? WP : BP;
    int them_pawn = (color == WHITE) ? BP : WP;

    for (int r = 0; r < 8; ++r) {
        int target = (r << 4) + file;
        if (pos.board[target] == us_pawn) friendly_pawn_present = true;
        if (pos.board[target] == them_pawn) enemy_pawn_present = true;
    }

    if (!friendly_pawn_present && !enemy_pawn_present) {
        score += 24; // Open file rook
    } else if (!friendly_pawn_present && enemy_pawn_present) {
        score += 12; // Semi-open file rook
    }
    return score;
}

bool is_outpost(const Position& pos, int sq, int color) {
    int rank = sq >> 4;
    int file = sq & 7;
    if (color == WHITE) {
        if (rank < 3 || rank > 5) return false;
        int bp = BP;
        for (int r = rank; r < 8; ++r) {
            if (file > 0 && pos.board[(r << 4) + file - 1] == bp) return false;
            if (file < 7 && pos.board[(r << 4) + file + 1] == bp) return false;
        }
    } else {
        if (rank < 2 || rank > 4) return false;
        int wp = WP;
        for (int r = rank; r >= 0; --r) {
            if (file > 0 && pos.board[(r << 4) + file - 1] == wp) return false;
            if (file < 7 && pos.board[(r << 4) + file + 1] == wp) return false;
        }
    }
    return true;
}

int get_mobility_bonus(const Position& pos, int sq, int piece) {
    int moves_count = 0;
    int color = get_color(piece);
    int type = get_piece_type(piece);

    if (type == WN) {
        for (int offset : knight_offsets) {
            int to = sq + offset;
            if (!(to & 0x88) && (pos.board[to] == EMPTY || get_color(pos.board[to]) != color)) {
                moves_count++;
            }
        }
        return moves_count * 3;
    } else if (type == WB) {
        for (int offset : bishop_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                if (pos.board[to] == EMPTY) {
                    moves_count++;
                } else {
                    if (get_color(pos.board[to]) != color) moves_count++;
                    break;
                }
                to += offset;
            }
        }
        return moves_count * 2;
    } else if (type == WR) {
        for (int offset : rook_offsets) {
            int to = sq + offset;
            while (!(to & 0x88)) {
                if (pos.board[to] == EMPTY) {
                    moves_count++;
                } else {
                    if (get_color(pos.board[to]) != color) moves_count++;
                    break;
                }
                to += offset;
            }
        }
        return moves_count * 2;
    }
    return 0;
}

// Separate evaluation of pawns using dedicated pawn cache
void evaluate_pawns(const Position& pos, int& pawn_score_mg, int& pawn_score_eg) {
    uint64_t pawn_hash = 0;

    // Build isolated pawn key
    for (int i = 0; i < pos.piece_count[WP]; ++i) pawn_hash ^= piece_keys[WP][pos.piece_list[WP][i]];
    for (int i = 0; i < pos.piece_count[BP]; ++i) pawn_hash ^= piece_keys[BP][pos.piece_list[BP][i]];

    int idx = pawn_hash % PAWN_TABLE_SIZE;
    if (pawn_table[idx].key == pawn_hash) {
        pawn_score_mg = pawn_table[idx].score_mg;
        pawn_score_eg = pawn_table[idx].score_eg;
        return;
    }

    int mg_sum = 0;
    int eg_sum = 0;

    // Evaluate White Pawns
    for (int i = 0; i < pos.piece_count[WP]; ++i) {
        int sq = pos.piece_list[WP][i];
        int r = sq >> 4;
        int f = sq & 7;
        int pst_idx = (7 - r) * 8 + f;

        int mg = mg_value[WP] + mg_pawn_table[pst_idx];
        int eg = eg_value[WP] + eg_pawn_table[pst_idx];

        if (is_pawn_isolated(pos, sq, WHITE)) { mg -= 15; eg -= 18; }
        if (is_pawn_doubled(pos, sq, WHITE)) { mg -= 10; eg -= 14; }
        if (is_pawn_passed(pos, sq, WHITE)) {
            int passed_bonus = r * r * 3;
            mg += passed_bonus;
            eg += passed_bonus * 1.5;
        }

        mg_sum += mg;
        eg_sum += eg;
    }

    // Evaluate Black Pawns
    for (int i = 0; i < pos.piece_count[BP]; ++i) {
        int sq = pos.piece_list[BP][i];
        int r = sq >> 4;
        int f = sq & 7;
        int pst_idx = r * 8 + f;

        int mg = mg_value[BP] + mg_pawn_table[pst_idx];
        int eg = eg_value[BP] + eg_pawn_table[pst_idx];

        if (is_pawn_isolated(pos, sq, BLACK)) { mg -= 15; eg -= 18; }
        if (is_pawn_doubled(pos, sq, BLACK)) { mg -= 10; eg -= 14; }
        if (is_pawn_passed(pos, sq, BLACK)) {
            int passed_bonus = (7 - r) * (7 - r) * 3;
            mg += passed_bonus;
            eg += passed_bonus * 1.5;
        }

        mg_sum -= mg;
        eg_sum -= eg;
    }

    pawn_table[idx].key = pawn_hash;
    pawn_table[idx].score_mg = mg_sum;
    pawn_table[idx].score_eg = eg_sum;

    pawn_score_mg = mg_sum;
    pawn_score_eg = eg_sum;
}

int evaluate(const Position& pos) {
    int mg[2] = {0, 0};
    int eg[2] = {0, 0};
    int phase = 0;

    int white_bishops = pos.piece_count[WB];
    int black_bishops = pos.piece_count[BB];

    // Load pawn values from specific cache
    int pawn_score_mg = 0;
    int pawn_score_eg = 0;
    evaluate_pawns(pos, pawn_score_mg, pawn_score_eg);

    mg[WHITE] += pawn_score_mg;
    eg[WHITE] += pawn_score_eg;

    // Evaluate non-pawn pieces
    for (int p_type = WN; p_type <= BK; ++p_type) {
        if (p_type == WP || p_type == BP) continue;

        int color = get_color(p_type);
        int count = pos.piece_count[p_type];

        // Dynamic scale boundaries
        if (p_type == WN || p_type == BN || p_type == WB || p_type == BB) phase += count * 1;
        else if (p_type == WR || p_type == BR) phase += count * 2;
        else if (p_type == WQ || p_type == BQ) phase += count * 4;

        for (int i = 0; i < count; ++i) {
            int sq = pos.piece_list[p_type][i];
            int r = sq >> 4;
            int f = sq & 7;
            int idx = r * 8 + f;
            if (color == WHITE) idx = (7 - r) * 8 + f;

            int mg_val = mg_value[p_type];
            int eg_val = eg_value[p_type];

            switch (p_type) {
                case WN: case BN:
                    mg_val += mg_knight_table[idx];
                    eg_val += eg_knight_table[idx];
                    mg_val += get_mobility_bonus(pos, sq, p_type);
                    if (is_outpost(pos, sq, color)) mg_val += 15;
                    break;

                case WB: case BB:
                    mg_val += mg_bishop_table[idx];
                    eg_val += eg_bishop_table[idx];
                    mg_val += get_mobility_bonus(pos, sq, p_type);
                    if (is_outpost(pos, sq, color)) mg_val += 10;
                    break;

                case WR: case BR:
                    mg_val += mg_rook_table[idx];
                    eg_val += eg_rook_table[idx];
                    mg_val += evaluate_rook_files(pos, sq, color);
                    break;

                case WQ: case BQ:
                    mg_val += mg_queen_table[idx];
                    eg_val += eg_queen_table[idx];
                    break;

                case WK: case BK:
                    mg_val += mg_king_table[idx];
                    eg_val += eg_king_table[idx];
                    mg_val += evaluate_king_safety(pos, sq, color);
                    break;
            }

            mg[color] += mg_val;
            eg[color] += eg_val;
        }
    }

    if (phase > 24) phase = 24;

    int mg_score = mg[WHITE] - mg[BLACK];
    int eg_score = eg[WHITE] - eg[BLACK];

    int score = ((mg_score * phase) + (eg_score * (24 - phase))) / 24;

    if (white_bishops >= 2) score += 30;
    if (black_bishops >= 2) score -= 30;

    return (pos.side == WHITE) ? score : -score;
}

// ============================================================================
// AUXILIARY UTILITY SUBROUTINES
// ============================================================================

void check_time() {
    if (nodes_searched % 1024 == 0) {
        // Standard time-based limit check
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration<double, std::milli>(now - search_start).count();
        if (elapsed >= search_time_limit_ms) {
            search_stopped = true;
        }

        // Added asynchronous stdin check to allow immediate interruption by Arena Chess
        #ifdef _WIN32
        static HANDLE stdin_h = GetStdHandle(STD_INPUT_HANDLE);
        DWORD bytes_avail = 0;
        if (PeekNamedPipe(stdin_h, NULL, 0, NULL, &bytes_avail, NULL) && bytes_avail > 0) {
            std::string line;
            if (std::getline(std::cin, line)) {
                std::stringstream ss(line);
                std::string cmd;
                ss >> cmd;
                if (cmd == "stop") {
                    search_stopped = true;
                } else if (cmd == "quit") {
                    search_stopped = true;
                    exit(0);
                }
            }
        }
        #else
        struct timeval tv = {0, 0};
        fd_set readfds;
        FD_ZERO(&readfds);
        FD_SET(STDIN_FILENO, &readfds);
        if (select(STDIN_FILENO + 1, &readfds, NULL, NULL, &tv) > 0) {
            std::string line;
            if (std::getline(std::cin, line)) {
                std::stringstream ss(line);
                std::string cmd;
                ss >> cmd;
                if (cmd == "stop") {
                    search_stopped = true;
                } else if (cmd == "quit") {
                    search_stopped = true;
                    exit(0);
                }
            }
        }
        #endif
    }
}

void score_moves(const Position& pos, MoveList& list, const Move& pv_move, int ply, const Move& prev_move) {
    for (int i = 0; i < list.count; ++i) {
        Move& m = list.moves[i];
        if (m == pv_move) {
            m.score = 2500000;
            continue;
        }

        int attacker = pos.board[m.from];
        int victim = pos.board[m.to];

        if (victim != EMPTY) {
            int value_bonus = see(const_cast<Position&>(pos), m.from, m.to);
            if (value_bonus >= 0) {
                m.score = 100000 + (mg_value[victim] * 10) - mg_value[attacker];
            } else {
                m.score = 50000 + (mg_value[victim] * 10) - mg_value[attacker];
            }
        } else if (m.promoted != EMPTY) {
            m.score = 90000 + mg_value[m.promoted];
        } else if (ply < 128 && m == killer_moves[0][ply]) {
            m.score = 80000;
        } else if (ply < 128 && m == killer_moves[1][ply]) {
            m.score = 70000;
        } else {
            if (prev_move.to != NO_SQ) {
                int last_piece = pos.board[prev_move.to];
                if (last_piece != EMPTY && m == counter_moves[last_piece][prev_move.to]) {
                    m.score = 65000;
                    continue;
                }
            }
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

bool is_repetition(uint64_t hash) {
    for (int i = 0; i < repetition_count; ++i) {
        if (repetition_history[i] == hash) return true;
    }
    return false;
}

bool has_non_pawn_material(const Position& pos, int side) {
    int n = (side == WHITE) ? WN : BN;
    int bb = (side == WHITE) ? WB : BB;
    int r = (side == WHITE) ? WR : BR;
    int q = (side == WHITE) ? WQ : BQ;
    return (pos.piece_count[n] > 0 || pos.piece_count[bb] > 0 || pos.piece_count[r] > 0 || pos.piece_count[q] > 0);
}

void store_killer(const Move& m, int ply) {
    if (ply < 128) {
        if (!(killer_moves[0][ply] == m)) {
            killer_moves[1][ply] = killer_moves[0][ply];
            killer_moves[0][ply] = m;
        }
    }
}

void clear_history() {
    for (int p = 0; p < 13; ++p) {
        for (int sq = 0; sq < 128; ++sq) {
            history_moves[p][sq] /= 2;
        }
    }
}

void init_lmr_table() {
    for (int depth = 0; depth < 64; ++depth) {
        for (int count = 0; count < 256; ++count) {
            if (depth == 0 || count == 0) {
                lmr_table[depth][count] = 0;
            } else {
                lmr_table[depth][count] = static_cast<int>(0.75 + std::log(depth) * std::log(count) / 1.95);
            }
        }
    }
}

// ============================================================================
// QUIESCENCE SEARCH
// ============================================================================

int quiescence(Position& pos, int alpha, int beta) {
    check_time();
    if (search_stopped) return 0;

    nodes_searched++;

    int stand_pat = evaluate(pos);
    if (stand_pat >= beta) return beta;
    if (stand_pat > alpha) alpha = stand_pat;

    MoveList list;
    generate_captures(pos, list);
    score_moves(pos, list, {0, 0, 0, 0}, 0, {0, 0, 0, 0});

    for (int i = 0; i < list.count; ++i) {
        sort_moves(list, i);
        const Move& m = list.moves[i];

        if (see(pos, m.from, m.to) < 0) continue;

        UndoInfo undo;
        if (!make_move(pos, m, undo)) continue;

        int score = -quiescence(pos, -beta, -alpha);
        unmake_move(pos, m, undo);

        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
    }

    return alpha;
}

// ============================================================================
// MAIN ENGINE SEARCH ALGORITHM WITH SEVERAL ADVANCED EXTENSIONS
// ============================================================================

int search(Position& pos, int depth, int ply, int alpha, int beta, Move& best_move, const Move& pv_move, const Move& prev_move, bool can_extend = true) {
    check_time();
    if (search_stopped) return 0;

    if (ply > 0 && (is_repetition(pos.hash) || pos.halfmove_clock >= 100)) {
        return 0; 
    }

    int alpha_temp = std::max(alpha, -30000 + ply);
    int beta_temp = std::min(beta, 30000 - ply - 1);
    if (alpha_temp >= beta_temp) return alpha_temp;

    nodes_searched++;

    if (depth <= 0) return quiescence(pos, alpha, beta);

    int tt_score = 0;
    Move tt_move = {0, 0, 0, 0};
    if (tt_probe(pos.hash, depth, ply, alpha, beta, tt_score, tt_move)) {
        best_move = tt_move;
        return tt_score;
    }

    bool in_check = is_in_check(pos);
    bool pv_node = (beta - alpha > 1);

    int extension = 0;
    if (in_check) extension = 1;

    int static_eval = evaluate(pos);

    // 1. Static Null Move Pruning (Reverse Futility Pruning)
    if (depth <= 3 && !in_check && !pv_node) {
        int margin = 120 * depth;
        if (static_eval - margin >= beta) {
            return static_eval - margin;
        }
    }

    // 2. Singular Extension Heuristic
    Move singular_move = {0, 0, 0, 0};
    if (can_extend && depth >= 8 && tt_move.from != 0 && tt_score > -29000 && tt_score < 29000) {
        TTBucket& bucket = transposition_table[pos.hash % TT_SIZE];
        for (int i = 0; i < 4; ++i) {
            if (bucket.entries[i].key == pos.hash && bucket.entries[i].depth >= depth - 3) {
                int r_beta = tt_score - (2 * depth); // Margin barrier
                Move dummy = {0, 0, 0, 0};

                // Exclude singular move from searches to see if another move matches it
                int score = search(pos, depth - 3, ply + 1, r_beta - 1, r_beta, dummy, tt_move, prev_move, false);
                if (score < r_beta) {
                    extension = 1; // Uniquely best move, extend line
                    singular_move = tt_move;
                }
                break;
            }
        }
    }

    depth += extension;

    // 3. Null Move Pruning
    if (!in_check && depth >= 3 && has_non_pawn_material(pos, pos.side)) {
        pos.side = (pos.side == WHITE) ? BLACK : WHITE;
        pos.hash ^= side_key;
        int ep_saved = pos.enpassant;
        if (pos.enpassant != -1) pos.hash ^= ep_keys[pos.enpassant];
        pos.enpassant = -1;

        Move dummy_move = {0, 0, 0, 0};
        int reduction = 3 + depth / 6;
        int score = -search(pos, depth - 1 - reduction, ply + 1, -beta, -beta + 1, dummy_move, {0, 0, 0, 0}, {0, 0, 0, 0});

        pos.side = (pos.side == WHITE) ? BLACK : WHITE;
        pos.hash ^= side_key;
        pos.enpassant = ep_saved;
        if (pos.enpassant != -1) pos.hash ^= ep_keys[pos.enpassant];

        if (score >= beta) return beta;
    }

    // 4. Internal Iterative Deepening
    Move primary_ordering_move = (tt_move.from != 0 || tt_move.to != 0) ? tt_move : pv_move;
    if (depth >= 5 && pv_node && primary_ordering_move.from == 0) {
        Move iid_move = {0, 0, 0, 0};
        search(pos, depth - 2, ply, alpha, beta, iid_move, {0, 0, 0, 0}, prev_move);
        primary_ordering_move = iid_move;
    }

    // 5. Futility Pruning
    bool futility_pruning_active = false;
    if (depth == 1 && !in_check && !pv_node) {
        if (static_eval + 150 < alpha) {
            futility_pruning_active = true;
        }
    }

    MoveList list;
    generate_moves(pos, list);
    score_moves(pos, list, primary_ordering_move, ply, prev_move);

    int legal_moves = 0;
    int best_score = -1000000;
    Move local_best_move = {0, 0, 0, 0};
    int orig_alpha = alpha;

    for (int i = 0; i < list.count; ++i) {
        sort_moves(list, i);
        const Move& m = list.moves[i];

        // Skip singular duplicates in sub-search evaluations
        if (singular_move.from != 0 && m == singular_move) continue;

        bool is_quiet = (pos.board[m.to] == EMPTY && m.promoted == EMPTY);

        if (futility_pruning_active && is_quiet && legal_moves > 0) {
            continue;
        }

        // Late Move Pruning
        if (!pv_node && !in_check && depth <= 3 && is_quiet) {
            int lmp_threshold = 3 + (depth * depth);
            if (legal_moves >= lmp_threshold) continue;
        }

        UndoInfo undo;
        if (!make_move(pos, m, undo)) continue;

        repetition_history[repetition_count++] = pos.hash;
        legal_moves++;

        Move temp_move = {0, 0, 0, 0};
        int score = 0;

        // 6. Principal Variation Search (PVS) with Late Move Reduction (LMR)
        if (legal_moves == 1) {
            score = -search(pos, depth - 1, ply + 1, -beta, -alpha, temp_move, {0, 0, 0, 0}, m);
        } else {
            int reduction = 0;
            if (depth >= 3 && legal_moves > 4 && !in_check && is_quiet) {
                reduction = lmr_table[depth][legal_moves];
                if (pv_node) reduction--;
                if (reduction < 0) reduction = 0;
            }

            if (reduction > 0) {
                score = -search(pos, depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, temp_move, {0, 0, 0, 0}, m);
                if (score > alpha && score < beta) {
                    score = -search(pos, depth - 1, ply + 1, -beta, -alpha, temp_move, {0, 0, 0, 0}, m);
                }
            } else {
                score = -search(pos, depth - 1, ply + 1, -alpha - 1, -alpha, temp_move, {0, 0, 0, 0}, m);
            }

            if (score > alpha && score < beta) {
                score = -search(pos, depth - 1, ply + 1, -beta, -alpha, temp_move, {0, 0, 0, 0}, m);
            }
        }

        repetition_count--;
        unmake_move(pos, m, undo);

        if (score > best_score) {
            best_score = score;
            local_best_move = m;
        }

        if (score >= beta) {
            if (is_quiet) {
                store_killer(m, ply);
                history_moves[pos.board[m.from]][m.to] += depth * depth;

                if (prev_move.to != NO_SQ) {
                    int last_piece = pos.board[prev_move.to];
                    if (last_piece != EMPTY) {
                        counter_moves[last_piece][prev_move.to] = m;
                    }
                }
            }
            tt_store(pos.hash, depth, ply, TT_BETA, beta, m);
            best_move = m;
            return beta;
        }
        if (score > alpha) {
            alpha = score;
        }
    }

    if (legal_moves == 0) {
        if (in_check) {
            return -30000 + ply;
        } else {
            return 0;
        }
    }

    int flag = (alpha <= orig_alpha) ? TT_ALPHA : TT_EXACT;
    tt_store(pos.hash, depth, ply, flag, alpha, local_best_move);

    best_move = local_best_move;
    return alpha;
}

// ============================================================================
// ITERATIVE DEEPENING CONTROL WITH ASPIRATION WINDOWS
// ============================================================================

Move iterative_deepening(Position& pos, double time_limit_ms) {
    search_start = std::chrono::steady_clock::now();
    search_time_limit_ms = time_limit_ms;
    search_stopped = false;
    nodes_searched = 0;

    tt_current_age++;
    clear_history();

    Move last_completed_best_move = {0, 0, 0, 0};

    // Fast fallback initial generation
    MoveList list;
    generate_moves(pos, list);
    for (int i = 0; i < list.count; ++i) {
        UndoInfo undo;
        if (make_move(pos, list.moves[i], undo)) {
            last_completed_best_move = list.moves[i];
            unmake_move(pos, list.moves[i], undo);
            break;
        }
    }

    int previous_score = 0;
    int alpha = -1000000;
    int beta = 1000000;

    for (int depth = 1; depth <= current_max_depth; ++depth) {
        Move current_best_move = {0, 0, 0, 0};
        int score = 0;

        // Aspiration Windows Heuristic
        if (depth >= 5) {
            int delta = 24;
            alpha = previous_score - delta;
            beta = previous_score + delta;

            while (true) {
                if (alpha < -25000) alpha = -1000000;
                if (beta > 25000) beta = 1000000;

                score = search(pos, depth, 0, alpha, beta, current_best_move, last_completed_best_move, {0, 0, 0, 0});

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
            score = search(pos, depth, 0, -1000000, 1000000, current_best_move, last_completed_best_move, {0, 0, 0, 0});
        }

        if (search_stopped) break;

        previous_score = score;
        last_completed_best_move = current_best_move;

        auto now = std::chrono::steady_clock::now();
        double elapsed_ms = std::chrono::duration<double, std::milli>(now - search_start).count();
        double nps = (elapsed_ms > 0) ? (nodes_searched / (elapsed_ms / 1000.0)) : 0;

        std::cout << "info depth " << depth << " score cp " << score
                  << " nodes " << nodes_searched << " nps " << (int)nps
                  << " time " << (int)elapsed_ms << " pv "
                  << square_to_uci(last_completed_best_move.from)
                  << square_to_uci(last_completed_best_move.to);
        if (last_completed_best_move.promoted != EMPTY) {
            std::cout << piece_to_promotion_char(last_completed_best_move.promoted);
        }
        std::cout << std::endl;

        if (score > 25000 || score < -25000) break;
    }

    return last_completed_best_move;
}

// ============================================================================
// PARSERS & FILE/DATABASE PARSING MECHANISMS
// ============================================================================

void load_fen(Position& pos, const std::string& fen) {
    std::memset(pos.board, EMPTY, sizeof(pos.board));
    std::memset(pos.piece_list, 0, sizeof(pos.piece_list));
    std::memset(pos.piece_count, 0, sizeof(pos.piece_count));
    std::memset(pos.piece_index, -1, sizeof(pos.piece_index));

    pos.side = WHITE;
    pos.castling = 0;
    pos.enpassant = -1;
    pos.halfmove_clock = 0;
    pos.fullmove_number = 1;

    std::stringstream ss(fen);
    std::string board_part, active_part, castle_part, ep_part, half_str, full_str;
    ss >> board_part >> active_part >> castle_part >> ep_part >> half_str >> full_str;

    int rank = 7;
    int file = 0;
    for (char c : board_part) {
        if (c == '/') {
            rank--; file = 0;
        } else if (std::isdigit(c)) {
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
            add_piece_to_lists(pos, sq, piece);
            file++;
        }
    }

    if (active_part == "b") pos.side = BLACK;

    for (char c : castle_part) {
        if (c == 'K') pos.castling |= WK_CASTLE;
        if (c == 'Q') pos.castling |= WQ_CASTLE;
        if (c == 'k') pos.castling |= BK_CASTLE;
        if (c == 'q') pos.castling |= BQ_CASTLE;
    }

    if (ep_part != "-" && ep_part.length() >= 2) {
        pos.enpassant = uci_to_square(ep_part);
    }

    if (!half_str.empty()) pos.halfmove_clock = std::stoi(half_str);
    if (!full_str.empty()) pos.fullmove_number = std::stoi(full_str);

    pos.hash = generate_hash(pos);
}

std::vector<std::string> parse_pgn_to_san(const std::string& pgn) {
    std::vector<std::string> san_moves;
    std::stringstream ss(pgn);
    std::string token;
    while (ss >> token) {
        if (token.find('.') != std::string::npos) {
            size_t dot_pos = token.find_last_of('.');
            if (dot_pos != std::string::npos && dot_pos < token.length() - 1) {
                std::string actual_move = token.substr(dot_pos + 1);
                if (!actual_move.empty()) san_moves.push_back(actual_move);
            }
            continue;
        }
        san_moves.push_back(token);
    }
    return san_moves;
}

bool move_matches_san(const Position& pos, const Move& m, std::string san) {
    if (san.empty()) return false;

    if (san.back() == '+' || san.back() == '#') {
        san.pop_back();
    }

    int piece = pos.board[m.from];
    int piece_type = get_piece_type(piece);
    int us = pos.side;

    if (san == "O-O" || san == "0-0") {
        if (us == WHITE) return (piece == WK && m.from == E1 && m.to == G1);
        else return (piece == BK && m.from == E8 && m.to == G8);
    }
    if (san == "O-O-O" || san == "0-0-0") {
        if (us == WHITE) return (piece == WK && m.from == E1 && m.to == C1);
        else return (piece == BK && m.from == E8 && m.to == C8);
    }

    int promo_piece = EMPTY;
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
        if (!san.empty() && std::isupper(san.back()) && (piece_type == WP)) {
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

    size_t x_pos = san.find('x');
    if (x_pos != std::string::npos) san.erase(x_pos, 1);

    char san_piece_char = san[0];
    int target_piece_type = EMPTY;
    bool is_pawn = false;

    if (san_piece_char == 'N') target_piece_type = WN;
    else if (san_piece_char == 'B') target_piece_type = WB;
    else if (san_piece_char == 'R') target_piece_type = WR;
    else if (san_piece_char == 'Q') target_piece_type = WQ;
    else if (san_piece_char == 'K') target_piece_type = WK;
    else {
        is_pawn = true;
        target_piece_type = WP;
    }

    if (piece_type != target_piece_type) return false;

    std::string rest = is_pawn ? san : san.substr(1);
    if (rest.length() < 2) return false;

    std::string target_sq_str = rest.substr(rest.length() - 2);
    int dest_sq = uci_to_square(target_sq_str);
    if (m.to != dest_sq) return false;

    std::string disambig = rest.substr(0, rest.length() - 2);
    if (!disambig.empty()) {
        char file_disambig = ' ';
        char rank_disambig = ' ';
        if (disambig.length() == 1) {
            if (disambig[0] >= 'a' && disambig[0] <= 'h') file_disambig = disambig[0];
            else if (disambig[0] >= '1' && disambig[0] <= '8') rank_disambig = disambig[0];
        } else if (disambig.length() == 2) {
            file_disambig = disambig[0];
            rank_disambig = disambig[1];
        }

        int from_file = 'a' + (m.from & 7);
        int from_rank = '1' + (m.from >> 4);

        if (file_disambig != ' ' && from_file != file_disambig) return false;
        if (rank_disambig != ' ' && from_rank != rank_disambig) return false;
    }

    Position temp = pos;
    UndoInfo undo;
    return make_move(temp, m, undo);
}

std::vector<std::string> san_to_uci_sequence(const std::vector<std::string>& san_moves) {
    Position temp_board;
    load_fen(temp_board, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");

    std::vector<std::string> uci_seq;
    for (const std::string& san : san_moves) {
        MoveList list;
        generate_moves(temp_board, list);
        Move matched_move = {0, 0, 0, 0};
        bool found = false;

        for (int i = 0; i < list.count; ++i) {
            if (move_matches_san(temp_board, list.moves[i], san)) {
                matched_move = list.moves[i];
                found = true;
                break;
            }
        }

        if (!found) return {};

        std::string uci_str = square_to_uci(matched_move.from) + square_to_uci(matched_move.to);
        if (matched_move.promoted != EMPTY) {
            uci_str += piece_to_promotion_char(matched_move.promoted);
        }
        uci_seq.push_back(uci_str);

        UndoInfo undo;
        if (!make_move(temp_board, matched_move, undo)) return {};
    }
    return uci_seq;
}

void load_fallback_book() {
    opening_book[{}].push_back("e2e4");
    opening_book[{}].push_back("d2d4");
    opening_book[{}].push_back("g1f3");
    opening_book[{}].push_back("c2c4");

    opening_book[{"e2e4"}].push_back("e7e5");
    opening_book[{"e2e4"}].push_back("c7c5");
    opening_book[{"e2e4"}].push_back("e7e6");
    opening_book[{"e2e4"}].push_back("c7c6");

    opening_book[{"d2d4"}].push_back("d7d5");
    opening_book[{"d2d4"}].push_back("g8f6");

    opening_book[{"g1f3"}].push_back("d7d5");
    opening_book[{"g1f3"}].push_back("g8f6");

    opening_book[{"e2e4", "c7c5"}].push_back("g1f3");
    opening_book[{"e2e4", "e7e5"}].push_back("g1f3");
    opening_book[{"d2d4", "g8f6"}].push_back("c2c4");
    opening_book[{"d2d4", "d7d5"}].push_back("c2c4");

    opening_book[{"e2e4", "c7c5", "g1f3"}].push_back("d7d6");
    opening_book[{"e2e4", "c7c5", "g1f3"}].push_back("e7e6");
    opening_book[{"e2e4", "c7c5", "g1f3"}].push_back("b8c6");
}

void load_opening_book() {
    load_fallback_book();

    std::ifstream file("chess_openings_comprehensive.txt");
    if (!file.is_open()) return;

    std::string line;
    std::getline(file, line); // Skip headers

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

// ============================================================================
// PARSERS FOR UCI PROTOCOL STRINGS
// ============================================================================

void parse_position(Position& pos, const std::string& cmd) {
    std::stringstream ss(cmd);
    std::string dummy, type;
    ss >> dummy >> type;

    uci_moves_played.clear();
    repetition_count = 0;

    if (type == "startpos") {
        load_fen(pos, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    } else if (type == "fen") {
        std::string fen_string = "";
        std::string part;
        for (int i = 0; i < 6; ++i) {
            ss >> part; fen_string += part + " ";
        }
        load_fen(pos, fen_string);
    }

    std::string moves_token;
    if (ss >> moves_token && moves_token == "moves") {
        std::string move_str;
        while (ss >> move_str) {
            MoveList list;
            generate_moves(pos, list);
            bool found = false;
            for (int i = 0; i < list.count; ++i) {
                Move m = list.moves[i];
                std::string current_m_str = square_to_uci(m.from) + square_to_uci(m.to);
                if (m.promoted != EMPTY) {
                    current_m_str += piece_to_promotion_char(m.promoted);
                }
                if (current_m_str == move_str) {
                    UndoInfo undo;
                    if (make_move(pos, m, undo)) {
                        repetition_history[repetition_count++] = pos.hash;
                        uci_moves_played.push_back(move_str);
                        found = true;
                        break;
                    }
                }
            }
            // Added safe validation and formatting guard checks
            if (!found && move_str.length() >= 4) {
                int from = uci_to_square(move_str.substr(0, 2));
                int to = uci_to_square(move_str.substr(2, 2));
                if (from != -1 && to != -1) {
                    int promo = EMPTY;
                    if (move_str.length() == 5) {
                        char pc = move_str[4];
                        if (pos.side == WHITE) {
                            if (pc == 'q') promo = WQ;
                            else if (pc == 'r') promo = WR;
                            else if (pc == 'b') promo = WB;
                            else if (pc == 'n') promo = WN;
                        } else {
                            if (pc == 'q') promo = BQ;
                            else if (pc == 'r') promo = BR;
                            else if (pc == 'b') promo = BB;
                            else if (pc == 'n') promo = BN;
                        }
                    }
                    Move m{from, to, promo, 0};
                    UndoInfo undo;
                    if (make_move(pos, m, undo)) {
                        repetition_history[repetition_count++] = pos.hash;
                        uci_moves_played.push_back(move_str);
                    }
                }
            }
        }
    }
}

void parse_go(const Position& pos, const std::string& cmd) {
    if (opening_book.count(uci_moves_played) > 0) {
        const auto& book_moves = opening_book[uci_moves_played];
        if (!book_moves.empty()) {
            static std::mt19937 rng(static_cast<unsigned>(std::chrono::system_clock::now().time_since_epoch().count()));
            std::uniform_int_distribution<size_t> dist(0, book_moves.size() - 1);
            std::string chosen_uci = book_moves[dist(rng)];

            MoveList list;
            generate_moves(pos, list);
            bool found_legal = false;
            for (int i = 0; i < list.count; ++i) {
                Move m = list.moves[i];
                std::string current_m_str = square_to_uci(m.from) + square_to_uci(m.to);
                if (m.promoted != EMPTY) {
                    current_m_str += piece_to_promotion_char(m.promoted);
                }
                if (current_m_str == chosen_uci) {
                    Position temp = pos;
                    UndoInfo undo;
                    if (make_move(temp, m, undo)) {
                        found_legal = true;
                        break;
                    }
                }
            }

            if (found_legal) {
                std::cout << "info string Playing book move: " << chosen_uci << std::endl;
                std::cout << "bestmove " << chosen_uci << std::endl;
                return;
            }
        }
    }

    std::stringstream ss(cmd);
    std::string token;
    ss >> token;

    current_max_depth = 64;
    double time_limit_ms = 2000.0;

    int wtime = -1, btime = -1;
    int winc = 0, binc = 0;
    int movestogo = 40;

    while (ss >> token) {
        if (token == "depth") {
            ss >> current_max_depth;
            time_limit_ms = 10000000.0;
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

    if (pos.side == WHITE && wtime != -1) {
        time_limit_ms = (double)wtime / movestogo + (double)winc * 0.8;
        if (time_limit_ms < 50) time_limit_ms = 50;
    } else if (pos.side == BLACK && btime != -1) {
        time_limit_ms = (double)btime / movestogo + (double)binc * 0.8;
        if (time_limit_ms < 50) time_limit_ms = 50;
    }

    Move best = iterative_deepening(const_cast<Position&>(pos), time_limit_ms);

    std::cout << "bestmove " << square_to_uci(best.from) << square_to_uci(best.to);
    if (best.promoted != EMPTY) {
        std::cout << piece_to_promotion_char(best.promoted);
    }
    std::cout << std::endl;
}

// ============================================================================
// SYSTEM BOOTSTRAP MAIN ROUTINE
// ============================================================================

int main() {
    std::setvbuf(stdout, NULL, _IONBF, 0);

    init_precalculations();
    init_zobrist();
    init_tt();
    init_pawn_table();
    init_lmr_table();
    load_opening_book();

    Position pos;
    load_fen(pos, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");

    std::string line;
    while (std::getline(std::cin, line)) {
        if (line.empty()) continue;
        std::stringstream ss(line);
        std::string cmd;
        ss >> cmd;

        if (cmd == "uci") {
            std::cout << "id name Core_Engine_v4.0" << std::endl;
            std::cout << "id author Iain Gaines" << std::endl;
            std::cout << "uciok" << std::endl;
        } else if (cmd == "isready") {
            std::cout << "readyok" << std::endl;
        } else if (cmd == "ucinewgame") {
            clear_tt();
            clear_pawn_table();
            uci_moves_played.clear();
            repetition_count = 0;
            load_fen(pos, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
        } else if (cmd == "position") {
            parse_position(pos, line);
        } else if (cmd == "go") {
            parse_go(pos, line);
        } else if (cmd == "quit") {
            break;
        }
    }

    if (transposition_table) delete[] transposition_table;
    if (pawn_table) delete[] pawn_table;
    return 0;
}
