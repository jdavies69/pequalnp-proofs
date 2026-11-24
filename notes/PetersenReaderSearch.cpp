// Numerical search for the remaining OR case of L-meta-2504.
// Build with c++ -O3 -std=c++17 PetersenReaderSearch.cpp -o search.
// Run once per possible NOT count from 0 through 14. Exit 0 means exhausted,
// 1 means a matching state, and 2 means an incomplete search or invalid input.
// The target is the nine-input Petersen-minus-a-vertex edge function. The
// suffix receives the nine inputs and the free signal x0 OR x6. Raw x6 is
// distinguished until consumed by at most one OR. All other wires are ordinary.
#include <algorithm>
#include <array>
#include <charconv>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>
// Each row holds one input variable on all positive samples, then on all
// negative samples. The first 78 pairs form three consecutive groups of 26
// witnesses.
const uint64_t raw[9][20] = {{0x500ce0e6f73818adULL, 0xa00070001fffc000ULL,
                              0xf3ffff540009ffffULL, 0xb3467928001524f4ULL,
                              0x15253d760006121ULL,  0x81d3255549525500ULL,
                              0x554fd58002444ULL,    0x58800155492aa92ULL,
                              0xaaaaaaaaa7a99660ULL, 0x4caaULL,
                              0x712100580b3818adULL, 0x2a8835440a888403ULL,
                              0x212a200551009510ULL, 0x9142392aa2000000ULL,
                              0x200200926a842000ULL, 0x80d3200000020154ULL,
                              0xc880004919222044ULL, 0x58a910000000082ULL,
                              0x20001018620ULL,      0x4c00ULL},
                             {0x800295a5c300a110ULL, 0xc0007ffffffff014ULL,
                              0x9c800198000e4000ULL, 0x4c0981fffff9c758ULL,
                              0x19c6267800062c6ULL,  0x61c3e66719c6600ULL,
                              0x6672660003c00ULL,    0x2010001998e3331cULL,
                              0xccccccccc4ce1860ULL, 0x210ccULL,
                              0x860e9f208000a110ULL, 0x5046482350470a54ULL,
                              0x84c1180a0882608cULL, 0x400804410c0c148ULL,
                              0x180c222490434042ULL, 0x2040800300c0282ULL,
                              0x460212024118c00ULL,  0x201408c00060100dULL,
                              0x400040444060840ULL,  0x21000ULL},
                             {0x831f5808c55602ULL,   0xffff9fffe0001180ULL,
                              0x1f0001e0000f8000ULL, 0x708e1e30001e079fULL,
                              0x1e07c79ffff9318ULL,  0x1863c78781e07800ULL,
                              0x787c780003a08ULL,    0xc1e0001e1f03c3e0ULL,
                              0xf0f0f0f0f8f01f92ULL, 0xf0ULL,
                              0x8d0600234c55602ULL,  0x6281314862831a8ULL,
                              0xb18a020c5058c50ULL,  0x708e0a318a020281ULL,
                              0xa000040026141308ULL, 0x801400080000830ULL,
                              0x428082c1830a3208ULL, 0xc1e18500030000e0ULL,
                              0x8000292ULL,          0x0ULL},
                             {0xe6208a0000c6d602ULL,
                              0xffffe00000000e45ULL,
                              0xe00001fffff00000ULL,
                              0x80f01fc0001ff81fULL,
                              0x1ff807e00001c1fULL,
                              0xe07c07f801ff8000ULL,
                              0x7f807ffffc070ULL,
                              0x600001fe003fc00ULL,
                              0xff00ff00ffe004ULL,
                              0x60ffULL,
                              0x8607115809028000ULL,
                              0x60d3606900d20200ULL,
                              0xe00348041aa001a4ULL,
                              0x805015c03440480aULL,
                              0x4806803e00c90417ULL,
                              0xa07c0000000f8006ULL,
                              0xd20000008348070ULL,
                              0x6001a4000001400ULL,
                              0x2a004ULL,
                              0x6000ULL},
                             {0x8208600234200820ULL, 0xa44ULL,
                              0x1ffffffffffULL,      0xffe000001fffe0ULL,
                              0x1ffff8000001fe0ULL,  0xff8007fffe000000ULL,
                              0x7fff800000380ULL,    0xf800001ffffc0000ULL,
                              0xff0000ffff000018ULL, 0x380ffULL,
                              0x8d0802080000000ULL,  0x15240a92152429c4ULL,
                              0x54902aa4476a4aULL,   0xadc005488293e0ULL,
                              0x90092f0015121be0ULL, 0x5f000000b60000a8ULL,
                              0x1240abb006490380ULL, 0xf8052480036c0001ULL,
                              0x50000055e000018ULL,  0x38000ULL},
                             {0x8d602000018008dULL,
                              0x1b8ULL,
                              0xfffffe0000000000ULL,
                              0xff000000001fffffULL,
                              0xfe00000000001fffULL,
                              0x7ffffffffffULL,
                              0xfff80000000003ffULL,
                              0x1fffffffffULL,
                              0xffffff000000001fULL,
                              0xffULL,
                              0x600234804000ULL,
                              0x36001b0036183cULL,
                              0xce80dc000680006cULL,
                              0x6e0000000cc2dbebULL,
                              0xdc000000001b1fffULL,
                              0x92048800ULL,
                              0x3700000000d8299ULL,
                              0x6c001241424ULL,
                              0x1fULL,
                              0x0ULL},
                             {0x1108000100002150ULL,
                              0x2002ULL,
                              0x0ULL,
                              0xffffffffffe00000ULL,
                              0x1fffULL,
                              0xfffff80000000000ULL,
                              0x3ffULL,
                              0xffffffe000000000ULL,
                              0x1fULL,
                              0x3ff00ULL,
                              0x8440000040ULL,
                              0x1b800dc01b82000ULL,
                              0x6e00037000370ULL,
                              0xfbff7fb86f000000ULL,
                              0xe0000000019c1fbdULL,
                              0xfdfbf0000000000cULL,
                              0x1b800000006e03ffULL,
                              0x4ea8370000000000ULL,
                              0x1fULL,
                              0xe500ULL},
                             {0x1005808010000ULL,
                              0x10ULL,
                              0x0ULL,
                              0x0ULL,
                              0xffffffffffffe000ULL,
                              0xffffffffffffffffULL,
                              0x3ffULL,
                              0x0ULL,
                              0xffffffffffffffe0ULL,
                              0x3ffffULL,
                              0x6020040000000000ULL,
                              0x19c00ce019c00401ULL,
                              0x67000338003380ULL,
                              0x670000000ULL,
                              0xfabbed9e06000ULL,
                              0xf7feb800240b03cfULL,
                              0x9c00000004700166ULL,
                              0x6380000000001ULL,
                              0x50007055707ed60ULL,
                              0x3ff00ULL},
                             {0x7df0608812028040ULL,
                              0x5abULL,
                              0x0ULL,
                              0x0ULL,
                              0x0ULL,
                              0x0ULL,
                              0xfffffffffffffc00ULL,
                              0xffffffffffffffffULL,
                              0xffffffffffffffffULL,
                              0x3ffffULL,
                              0x79f80a0102500088ULL,
                              0x1e000f001e000583ULL,
                              0x780003c0003c00ULL,
                              0x780000000ULL,
                              0x1e000000ULL,
                              0xf0ULL,
                              0xe000abf9b7803c00ULL,
                              0xb157c000024800cbULL,
                              0x50007055f054fe0ULL,
                              0x31a00ULL}};
using namespace std;
constexpr int wordCount = 10;
using Words = array<uint64_t, wordCount>;
using Signature = array<Words, 2>;
using LiveWires = array<uint32_t, 16>;
struct Wire {
  uint64_t mask, left, right;
  Signature s;
  array<Words, 2> separation;
};
template <class T> struct Hash {
  size_t operator()(const T &s) const noexcept {
    uint64_t h = 0x65a5c09873095db7;
    for (int i = 0; i < (int)sizeof(s) / 8; i++) {
      uint64_t x;
      memcpy(&x, ((const unsigned char *)&s) + i * 8, 8);
      x ^= x >> 33;
      x *= 0xff51afd7ed558ccdULL;
      h = (h ^ x) * 0x9E3779B185EBCA87ULL;
    }
    return h ^ (h >> 30);
  }
};
const Words top = {0xffffffffffffffffULL, 0xffffffffffffffffULL,
                   0xffffffffffffffffULL, 0xffffffffffffffffULL,
                   0xffffffffffffffffULL, 0xffffffffffffffffULL,
                   0xffffffffffffffffULL, 0xffffffffffffffffULL,
                   0xffffffffffffffffULL, 0x3ffffULL};
Signature target{top, Words{}};
unordered_map<Signature, int, Hash<Signature>> ids;
vector<Wire> wires;
array<array<unordered_set<LiveWires, Hash<LiveWires>>, 15>, 16> failed;
uint64_t visited = 0, saved = 0;
int goal, tagged, ordinarySix;

int intern(const Signature &s) {
  auto ptr = ids.find(s);
  if (ptr != ids.end())
    return ptr->second;
  int count = wires.size();
  auto field = [&](int side, int chunk) {
    int bit = chunk * 26, j = bit / 64, shift = bit % 64;
    uint64_t w = s[side][j] >> shift;
    if (shift && shift + 26 > 64)
      w |= s[side][j + 1] << (64 - shift);
    return w & ((1ULL << 26) - 1);
  };
  uint64_t P = field(0, 0), pa = field(0, 1), pb = field(0, 2),
           na = field(1, 0), nb = field(1, 1), z = field(1, 2);
  Wire v{(~P | (na & nb)) & (~(pa | pb) | z), na & ~pb, nb & ~pa, s, {}};
  for (int j = 0; j < wordCount; j++) {
    v.separation[0][j] = s[0][j] & ~s[1][j];
    v.separation[1][j] = s[0][j] ^ s[1][j];
  }
  wires.push_back(v);
  ids[s] = count;
  return count;
}
bool full(const Words &a, const Words &b) {
  for (int j = 0; j < wordCount; j++)
    if ((a[j] | b[j]) != top[j])
      return false;
  return true;
}
Words join(Words a, const Words &b) {
  for (int j = 0; j < wordCount; j++)
    a[j] |= b[j];
  return a;
}
bool search(int remainingGates, int remainingNots, const LiveWires &v,
            int count) {
  if (remainingGates + 1 - remainingNots < count)
    return false;
  if (binary_search(v.begin(), v.begin() + count, goal))
    return true;
  if (remainingGates == 0 || count < 1)
    return false;
  auto &cache = failed[remainingGates][remainingNots];
  if (remainingGates >= 7 && cache.count(v))
    return false;
  ++visited;
  if (visited % 10000000 == 0)
    cerr << visited << " states, " << saved << " cached " << wires.size()
         << " signatures" << endl;
  if (saved >= 6000000 || wires.size() >= 3200000) {
    cerr << "memory quota " << saved << " " << wires.size() << " visits "
         << visited << endl;
    exit(2);
  }
  Words prefixCoverage[17] = {}, suffixCoverage[17] = {},
        positivePrefix[17] = {}, positiveSuffix[17] = {};
  for (int i = 0; i < count; i++) {
    prefixCoverage[i + 1] =
        join(prefixCoverage[i], wires[v[i]].separation[remainingNots > 0]);
    positivePrefix[i + 1] = join(positivePrefix[i], wires[v[i]].separation[0]);
  }
  if (prefixCoverage[count] != top)
    return false;
  // At equality each binary gate must merge two live wires and keep neither.
  // A unique positive witness for every wire precludes a single negation.
  // With no negations, use six-row obstructions to a read-once formula.
  if (remainingGates - remainingNots + 1 == count && remainingNots <= 1) {
    bool positive = remainingNots == 0;
    if (remainingNots == 1) {
      Words once{}, twice{};
      for (int i = 0; i < count; i++)
        for (int j = 0; j < wordCount; j++) {
          auto diff = wires[v[i]].separation[1][j];
          twice[j] |= once[j] & diff;
          once[j] |= diff;
        }
      positive = true;
      for (int i = 0; i < count && positive; i++) {
        bool ok = false;
        for (int j = 0; j < wordCount; j++)
          ok |= (wires[v[i]].separation[0][j] & ~twice[j]) != 0;
        positive = ok;
      }
      if (positive)
        return false;
    }
    if (remainingNots == 0) {
      uint64_t a = (1ULL << 26) - 1, l = 0, r = 0, b = 0;
      for (int i = 0; i < count; i++) {
        const auto &w = wires[v[i]];
        b = (b & w.mask) | (l & w.right) | (r & w.left);
        l = (l & w.mask) | (a & w.left);
        r = (r & w.mask) | (a & w.right);
        a &= w.mask;
      }
      if (b)
        return false;
    }
  }
  for (int i = count - 1; i >= 0; i--) {
    suffixCoverage[i] =
        join(suffixCoverage[i + 1], wires[v[i]].separation[remainingNots > 0]);
    positiveSuffix[i] = join(positiveSuffix[i + 1], wires[v[i]].separation[0]);
  }
  // Each mask records which operands remain available after this gate.
  auto child = [&](int i, int j, int mask, int id, int tn) {
    LiveWires out{};
    int z = 0;
    for (int a = 0; a < count; a++)
      if ((a != i || mask & 1) && (a != j || mask & 2))
        out[z++] = v[a];
    if (z + 1 > remainingGates + 1 - tn ||
        binary_search(out.begin(), out.begin() + z, id) ||
        binary_search(v.begin(), v.begin() + count, id))
      return false;
    int pos = lower_bound(out.begin(), out.begin() + z, id) - out.begin();
    move_backward(out.begin() + pos, out.begin() + z, out.begin() + z + 1);
    out[pos] = id;
    return search(remainingGates - 1, tn, out, z + 1);
  };
  for (int i = 0; i < count; i++) {
    Signature a = wires[v[i]].s;
    // A unary OR, or an OR whose other input simplifies to false, releases
    // an unrestricted copy. Any future gate may use that ordinary signal.
    if (v[i] == tagged && child(i, count, 0, ordinarySix, remainingNots))
      return true;
    if (v[i] != tagged && remainingNots && count <= remainingGates) {
      Signature s;
      for (int d = 0; d < 2; d++)
        for (int j = 0; j < wordCount; j++)
          s[d][j] = top[j] ^ a[d][j];
      Words separation{};
      for (int j = 0; j < wordCount; j++)
        separation[j] =
            remainingNots > 1 ? (s[0][j] ^ s[1][j]) : (s[0][j] & ~s[1][j]);
      Words rest = remainingNots > 1
                       ? join(prefixCoverage[i], suffixCoverage[i + 1])
                       : join(positivePrefix[i], positiveSuffix[i + 1]);
      bool rd = full(rest, separation);
      if ((rd || (count < remainingGates &&
                  full(remainingNots > 1 ? prefixCoverage[count]
                                         : positivePrefix[count],
                       separation)))) {
        int id = intern(s);
        if (((rd && child(i, count, 0, id, remainingNots - 1)) ||
             (count < remainingGates &&
              child(i, count, 1, id, remainingNots - 1))))
          return true;
      }
    }
    Words middle{};
    for (int j = i + 1; j < count; j++) {
      Signature b = wires[v[j]].s;
      Words rest = join(join(prefixCoverage[i], middle), suffixCoverage[j + 1]);
      for (int op = 0; op < 2; op++) {
        if (!op && (v[i] == tagged || v[j] == tagged))
          continue;
        Signature s;
        Words sp;
        for (int l = 0; l < wordCount; l++) {
          for (int d = 0; d < 2; d++)
            s[d][l] = op ? (a[d][l] | b[d][l]) : (a[d][l] & b[d][l]);
          sp[l] = remainingNots ? (s[0][l] ^ s[1][l]) : (s[0][l] & ~s[1][l]);
        }
        if ((s == a && v[i] != tagged) || (s == b && v[j] != tagged) ||
            s == Signature{} || s == Signature{top, top})
          continue;
        int id = -1;
        Words nc = join(rest, sp);
        for (int mask = 0; mask < 4; mask++) {
          if ((v[i] == tagged && (mask & 1)) || (v[j] == tagged && (mask & 2)))
            continue;
          if (count - 1 + __builtin_popcount((unsigned)mask) >
              remainingGates - remainingNots)
            continue;
          Words cov = nc;
          if (mask & 1)
            cov = join(cov, wires[v[i]].separation[remainingNots > 0]);
          if (mask & 2)
            cov = join(cov, wires[v[j]].separation[remainingNots > 0]);
          if (cov != top)
            continue;
          if (id < 0)
            id = intern(s);

          if (child(i, j, mask, id, remainingNots))
            return true;
        }
      }
      middle = join(middle, wires[v[j]].separation[remainingNots > 0]);
    }
  }
  if (remainingGates >= 7) {
    cache.insert(v);
    saved++;
  }
  return false;
}
bool edgeFunction(unsigned y) {
  constexpr int edges[][2] = {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}, {0, 5},
                              {1, 6}, {2, 7}, {3, 8}, {5, 7}, {6, 8}, {8, 5}};
  for (auto &edge : edges)
    if ((y >> edge[0] & 1) && (y >> edge[1] & 1))
      return true;
  return false;
}
bool validChart() {
  for (int word = 0; word < wordCount; word++)
    for (int bit = 0; bit < 64; bit++) {
      if (!(top[word] >> bit & 1))
        continue;
      for (int side = 0; side < 2; side++) {
        unsigned y = 0;
        for (int i = 0; i < 9; i++)
          y |= ((raw[i][side * wordCount + word] >> bit) & 1u) << i;
        if (edgeFunction(y) != (side == 0))
          return false;
      }
    }
  return true;
}
int main(int argc, char **argv) {
  int remainingNots = 0;
  if (argc != 2) {
    cerr << "Supply the number of NOT gates (0 through 14)." << endl;
    return 2;
  }
  string_view arg(argv[1]);
  auto [end, err] =
      from_chars(arg.data(), arg.data() + arg.size(), remainingNots);
  if (err != errc{} || end != arg.data() + arg.size() || remainingNots < 0 ||
      remainingNots > 14)
    return 2;
  if (!validChart()) {
    cerr << "Invalid positive/negative input pair." << endl;
    return 2;
  }
  LiveWires inputs{};
  intern(Signature{});
  intern(Signature{top, top});
  goal = intern(target);
  for (int p = 0; p < 9; p++) {
    Signature s{};
    memcpy(s.data(), raw[p], sizeof(s));
    inputs[p] = intern(s);
  }
  Signature pin{};
  for (int side = 0; side < 2; side++)
    for (int j = 0; j < wordCount; j++)
      pin[side][j] = wires[inputs[0]].s[side][j] | wires[inputs[6]].s[side][j];
  inputs[9] = intern(pin);
  ordinarySix = inputs[6];
  auto tagwire = wires[ordinarySix];
  tagged = wires.size();
  wires.push_back(tagwire);
  inputs[6] = tagged;
  sort(inputs.begin(), inputs.begin() + 10);
  vector<unsigned> bits(inputs.begin(), inputs.begin() + 10);
  unsigned roots = 0;
  bool possible = false;
  for (unsigned mask = 1; mask < (1u << bits.size()); mask++) {
    int count = __builtin_popcount(mask);
    if (count > 15 - remainingNots)
      continue;
    LiveWires v{};
    int s = 0;
    Words cover{};
    for (int i = 0; i < (int)bits.size(); i++)
      if (mask & (1u << i)) {
        v[s++] = bits[i];
        cover = join(cover, wires[bits[i]].separation[remainingNots > 0]);
      }
    if (cover != top)
      continue;
    roots++;
    if (search(14, remainingNots, v, count)) {
      possible = true;
      break;
    }
  }
  cout << "NOT gates " << remainingNots << " | roots " << roots << " | states "
       << visited << " | reached target " << boolalpha << possible << endl;
  return possible ? 1 : 0;
}
