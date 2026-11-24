// Enumerate live wire sets on 414 positive/negative Petersen assignment pairs.
// Arguments give the number of NOT gates and the two operands of the second OR.
// Operand 10 supplies false, so the menu includes unary and empty OR gates.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <unordered_set>
#include <map>
#include <vector>
#include "sample-words.hpp"

using Words = std::array<std::uint64_t, 7>;
using Signature = std::array<Words, 2>;
using State = std::array<unsigned, 16>;

const Words all = {~0ULL, ~0ULL, ~0ULL, ~0ULL, ~0ULL, ~0ULL, (1ULL << 30) - 1};
const Signature goal = {all, Words{}};
const Signature constantTrue = {all, all};

struct StateHash {
    size_t operator()(const State &state) const {
        size_t hash = 1469598103934665603ULL;
        for (unsigned id : state) hash = (hash ^ id) * 1099511628211ULL;
        return hash;
    }
};

struct Wire {
    Signature values;
    Words forward;
    Words either;
};

class Search {
public:
    unsigned intern(const Signature &values) {
        auto result = numbers.emplace(values, wires.size());
        if (result.second) {
            Wire wire{values, {}, {}};
            for (size_t j = 0; j < all.size(); ++j) {
                wire.forward[j] = values[0][j] & ~values[1][j];
                wire.either[j] = values[0][j] ^ values[1][j];
            }
            wires.push_back(wire);
        }
        return result.first->second;
    }

    bool possible(int gates, int nots, const State &state, int count) {
        if (count > gates + 1 - nots) return false;
        if (std::binary_search(state.begin(), state.begin() + count, goalId)) return true;
        if (gates == 0 || count == 0) return false;

        auto &cache = failed[gates][nots];
        if (gates >= 5 && cache.count(state)) return false;
        ++visited;
        if (!covers(state, count, nots)) return false;

        for (int i = 0; i < count; ++i) {
            const Signature left = wires[state[i]].values;
            if (nots > 0) {
                Signature inverted = left;
                for (auto &side : inverted)
                    for (size_t k = 0; k < all.size(); ++k) side[k] ^= all[k];
                for (int keep = 0; keep < 2; ++keep)
                    if (advance(gates, nots - 1, state, count, i, count, keep, inverted)) return true;
            }
            for (int j = i + 1; j < count; ++j) {
                const Signature right = wires[state[j]].values;
                for (bool useOr : {false, true}) {
                    Signature out{};
                    for (size_t side = 0; side < 2; ++side)
                        for (size_t k = 0; k < all.size(); ++k)
                            out[side][k] = useOr ? left[side][k] | right[side][k]
                                                : left[side][k] & right[side][k];
                    if (out == left || out == right || out == Signature{} || out == constantTrue) continue;
                    for (int keep = 0; keep < 4; ++keep)
                        if (advance(gates, nots, state, count, i, j, keep, out)) return true;
                }
            }
        }
        if (gates >= 5) cache.insert(state);
        return false;
    }

    bool covers(const State &state, int count, int nots) const {
        Words cover{};
        for (int i = 0; i < count; ++i) {
            const Wire &wire = wires[state[i]];
            const Words &separates = nots ? wire.either : wire.forward;
            for (size_t k = 0; k < all.size(); ++k) cover[k] |= separates[k];
        }
        return cover == all;
    }

    std::uint64_t visited = 0;
    unsigned goalId = 0;

private:
    bool advance(int gates, int remainingNots, const State &state, int count,
                 int left, int right, int keep, const Signature &out) {
        State next{};
        int size = 0;
        for (int i = 0; i < count; ++i) {
            if ((i != left || (keep & 1)) && (i != right || (keep & 2))) next[size++] = state[i];
        }
        if (size + 1 > gates - remainingNots) return false;
        // Check separation before interning. A missing pair can never be restored.
        Words coverage{};
        for (size_t k = 0; k < all.size(); ++k) {
            coverage[k] = remainingNots ? out[0][k] ^ out[1][k] : out[0][k] & ~out[1][k];
        }
        for (int i = 0; i < size; ++i) {
            const auto &wire = wires[next[i]];
            const auto &separates = remainingNots ? wire.either : wire.forward;
            for (size_t k = 0; k < all.size(); ++k) coverage[k] |= separates[k];
        }
        if (coverage != all) return false;

        unsigned id = intern(out);
        if (std::binary_search(state.begin(), state.begin() + count, id)) return false;
        next[size++] = id;
        std::sort(next.begin(), next.begin() + size);
        return possible(gates - 1, remainingNots, next, size);
    }

    std::map<Signature, unsigned> numbers;
    std::vector<Wire> wires;
    std::array<std::array<std::unordered_set<State, StateHash>, 14>, 14> failed;
};

int main(int argc, char **argv) {
    if (argc != 4) return 2;
    const int nots = std::atoi(argv[1]), a = std::atoi(argv[2]), b = std::atoi(argv[3]);
    if (nots < 0 || nots > 13 || a < 0 || a > 10 || b < a || b > 10) return 2;
    Search search;
    search.intern(Signature{});
    search.intern(constantTrue);
    search.goalId = search.intern(goal);

    std::array<Signature, 11> input{};
    for (int i = 0; i < 9; ++i)
        for (int side = 0; side < 2; ++side)
            std::copy_n(raw[i] + 7 * side, 7, input[i][side].begin());
    for (int side = 0; side < 2; ++side)
        for (size_t k = 0; k < all.size(); ++k) {
            input[9][side][k] = input[0][side][k] & input[3][side][k];
            input[10][side][k] = input[a][side][k] | input[b][side][k];
        }
    std::set<unsigned> unique;
    for (const auto &wire : input) {
        unsigned id = search.intern(wire);
        if (id > 1) unique.insert(id);
    }
    std::vector<unsigned> available(unique.begin(), unique.end());
    unsigned roots = 0;
    bool found = false;
    for (unsigned mask = 1; !found && mask < (1U << available.size()); ++mask) {
        State state{};
        int count = 0;
        for (size_t i = 0; i < available.size(); ++i)
            if (mask & (1U << i)) state[count++] = available[i];
        if (count > 14 - nots || !search.covers(state, count, nots)) continue;
        ++roots;
        found = search.possible(13, nots, state, count);
    }
    std::cout << a << ' ' << b << ' ' << nots << ' ' << roots << ' '
              << search.visited << ' ' << found << '\n';
}
