// C++17. Enumerate every legal change of one or two gates in each listed layout.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

using Mask = std::uint64_t;
constexpr int inputs = 14, gates = 27;
using Wires = std::array<Mask, inputs + gates>;
struct Gate { bool meet; int a, b; };
using Circuit = std::vector<Gate>;
using Edits = std::array<std::vector<Gate>, gates>;

Mask gate_value(Gate g, const Wires &w) {
    return g.meet ? w[g.a] & w[g.b] : w[g.a] | w[g.b];
}
void evaluate(const Circuit &c, Wires &w, int from = 0) {
    for (int i = from; i < gates; ++i) w[inputs + i] = gate_value(c[i], w);
}

Circuit layout(int kind) {
    Circuit c;
    auto gate = [&](bool meet, int a, int b) {
        c.push_back({meet, std::min(a,b), std::max(a,b)});
        return int(inputs + c.size() - 1);
    };
    auto point_or = [&](int l) {
        return gate(false, gate(false, l, (l+1)%7), (l+3)%7);
    };
    std::vector<int> stars;
    if (kind == 3) {
        for (int l = 0; l < 7; ++l) stars.push_back(point_or(l));
        for (int l = 0; l < 7; ++l) stars[l] = gate(true, stars[l], 7+l);
    } else {
        for (int l = 0; l < 7; ++l) {
            int s = gate(true, point_or(l), 7+l);
            if (kind == 0 && !stars.empty()) stars[0] = gate(false, stars[0], s);
            else stars.push_back(s);
        }
    }
    if (kind == 1) {
        for (int i = 1; i < 7; ++i) stars[0] = gate(false, stars[0], stars[i]);
    } else {
        while (stars.size() > 1) {
            std::vector<int> layer;
            for (size_t i = 0; i < stars.size(); i += 2)
                layer.push_back(i+1 == stars.size() ? stars[i] : gate(false, stars[i], stars[i+1]));
            stars = layer;
        }
    }
    assert(c.size() == gates && stars[0] == inputs + gates - 1);
    return c;
}

struct Tests {
    Wires boundary{}, value{}, direction{};
    Mask goal = 0;
    std::array<bool, 1<<inputs> truth{};
    Tests() {
        std::vector<std::pair<int,int>> edges;
        for (int l = 0; l < 7; ++l)
            for (int d : {0,1,3}) edges.emplace_back((l+d)%7, 7+l);
        for (int x = 0; x < int(truth.size()); ++x)
            for (auto [p,l] : edges)
                if ((x & (1<<p)) && (x & (1<<l))) truth[x] = true;
        int count = 0, positives = 0;
        for (int x = 0; x < int(truth.size()); ++x) {
            if (truth[x]) {
                if (__builtin_popcount(unsigned(x)) != 2) continue;
                ++positives;
            } else {
                bool maximal = true;
                for (int j = 0; j < inputs; ++j)
                    if (!(x & (1<<j)) && !truth[x | (1<<j)]) maximal = false;
                if (!maximal) continue;
            }
            assert(count < 64);
            Mask bit = Mask(1) << count++;
            if (truth[x]) goal |= bit;
            for (int j = 0; j < inputs; ++j) if (x & (1<<j)) boundary[j] |= bit;
        }
        assert(positives == 21 && count == 58);
        for (int i = 0; i < int(edges.size()); ++i) {
            auto [p,l] = edges[i];
            value[p] |= Mask(1) << i; direction[l] |= Mask(1) << i;
            value[l] |= Mask(1) << (21+i); direction[p] |= Mask(1) << (21+i);
        }
    }

    bool double_read(const Circuit &c) const {
        Wires v = value, d = direction;
        for (int i = 0; i < gates; ++i) {
            auto g = c[i];
            v[inputs+i] = gate_value(g, v);
            d[inputs+i] = g.meet ? (v[g.a] & d[g.b]) | (d[g.a] & v[g.b])
                                 : d[g.a] | d[g.b];
        }
        constexpr Mask flags = (Mask(1)<<21)-1;
        return ((~(d.back() | (d.back() >> 21))) & flags) != 0;
    }

    bool full_check(const Circuit &c) const {
        for (int base = 0; base < int(truth.size()); base+=64) {
            Wires w{};
            Mask goal_block = 0;
            for (int k = 0; k < 64; ++k) {
                Mask bit = Mask(1)<<k;
                if (truth[base+k]) goal_block |= bit;
                for (int j = 0; j < inputs; ++j)
                    if ((base+k) & (1<<j)) w[j] |= bit;
            }
            evaluate(c,w);
            if (w.back() != goal_block) return false;
        }
        return true;
    }
};

void search(int kind, const Tests &t) {
    Circuit c = layout(kind);
    assert(t.full_check(c) && !t.double_read(c));
    Edits edits;
    for (int i = 0; i < gates; ++i) {
        for (int a = 0; a < inputs+i; ++a)
            for (int b = a+1; b < inputs+i; ++b)
                for (bool meet : {false,true})
                    if (c[i].a != a || c[i].b != b || c[i].meet != meet)
                        edits[i].push_back({meet, a, b});
    }
    std::uint64_t single = 0, pairs = 0, correct1 = 0, correct2 = 0, both = 0;
    auto checked = [&]() { assert(t.full_check(c)); both += t.double_read(c); };
    for (int i = 0; i < gates; ++i) {
        auto original = c[i];
        for (auto first : edits[i]) {
            c[i] = first;
            Wires w = t.boundary;
            evaluate(c,w);
            ++single;
            if (w.back() == t.goal) { ++correct1; checked(); }
            for (int j = i+1; j < gates; ++j) {
                // Each assignment has a monotone unary suffix in wire (inputs+j).
                // Its two endpoint values determine the output for any edit at j.
                Wires lo = w, hi = w;
                lo[inputs+j] = 0; hi[inputs+j] = ~Mask(0);
                evaluate(c,lo,j+1); evaluate(c,hi,j+1);
                pairs += edits[j].size();
                if ((lo.back() & ~t.goal) || (t.goal & ~hi.back())) continue;
                auto saved = c[j];
                for (auto second : edits[j]) {
                    if ((lo.back() | (hi.back() & gate_value(second,w))) != t.goal) continue;
                    c[j] = second;
                    ++correct2; checked();
                }
                c[j] = saved;
            }
        }
        c[i] = original;
    }
    assert(single == 20565 && pairs == 201287619);
    std::cout << kind << ": singles " << single << ", pairs " << pairs
              << ", correct singles " << correct1 << ", correct pairs " << correct2
              << ", correct with a double read " << both << std::endl;
}

int main() {
    Tests t;
    for (int k = 0; k < 4; ++k) search(k,t);
}
