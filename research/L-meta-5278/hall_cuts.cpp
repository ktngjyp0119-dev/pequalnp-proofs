// c++ -O2 -std=c++17 hall_cuts.cpp -o hall && ./hall
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <unordered_set>
#include <vector>

using Mask = uint64_t;
constexpr Mask all = (Mask(1)<<52)-1;
int size(Mask m) { return __builtin_popcountll(m); }
void complete(Mask set, Mask choices, int left, std::unordered_set<Mask>& output) {
    if (!left) { output.insert(set); return; }
    while(choices) {
        Mask bit=choices & -choices;
        choices^=bit;
        complete(set|bit,choices,left-1,output);
    }
}
uint64_t choose(int n, int k) {
    uint64_t r=1;
    for(int i=1; i<=k; ++i) r=r*(n-i+1)/i;
    return r;
}
int main() {
    std::array<Mask,8192> points{},lines{};
    std::array<std::vector<int>,14> subsets;
    int id=0;
    for(int l=0;l<13;++l) for(int d:{0,1,3,9}) {
        points[1<<((l+d)%13)]|=Mask(1)<<id;
        lines[1<<l]|=Mask(1)<<id++;
    }
    for(int s=0;s<8192;++s) {
        if(s) {
            points[s]=points[s&-s]|points[s&(s-1)];
            lines[s]=lines[s&-s]|lines[s&(s-1)];
        }
        subsets[size(s)].push_back(s);
    }
    // If U has fewer than |U| neighbors, extend those neighbors to any
    // V of size |U|-1. All original flags from U to the complement of V
    // must have been removed. Enumerating these cuts covers every defect.
    std::array<std::set<Mask>,8> cuts;
    for(int u=1;u<=13;++u) for(int p:subsets[u]) for(int l:subsets[u-1]) {
        Mask cut=points[p]&~lines[l];
        int k=size(cut);
        if(k<=7) cuts[k].insert(cut);
    }
    std::vector<Mask> minimal;
    for(auto& group:cuts) for(Mask cut:group) {
        bool redundant=false;
        for(Mask m:minimal) if((m&cut)==m) { redundant=true; break; }
        if(!redundant) minimal.push_back(cut);
    }
    std::set<Mask> predicted;
    for(int i=0;i<13;++i) {
        predicted.insert(points[1<<i]); predicted.insert(lines[1<<i]);
        for(int j=0;j<i;++j) {
            int ij=(1<<i)|(1<<j);
            for(int k=0;k<13;++k) {
                Mask a=points[ij]&~lines[1<<k], b=lines[ij]&~points[1<<k];
                if(size(a)==6) predicted.insert(a);
                if(size(b)==6) predicted.insert(b);
            }
        }
    }
    assert(std::set<Mask>(minimal.begin(),minimal.end())==predicted);
    int stars=0,pairs=0;
    for(Mask m:minimal) { stars+=size(m)==4; pairs+=size(m)==6; }
    assert(stars==26 && pairs==156 && minimal.size()==182);
    std::cout<<"Minimal obstructions: "<<stars<<" stars, "<<pairs<<" pairs.\n";
    for(int r=0;r<=7;++r) {
        std::unordered_set<Mask> deficient;
        for(Mask m:minimal) if(size(m)<=r) complete(m,all^m,r-size(m),deficient);
        std::cout<<r<<" deleted: "<<deficient.size()<<" deficient, "
                 <<choose(52,r)-deficient.size()<<" perfect.\n";
    }
}
