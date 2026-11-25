// Enumerate all deletions of up to four flags from the order-three Singer plane.
// Build and run: c++ -O2 -std=c++17 plane_cover.cpp -o plane && ./plane
#include <array>
#include <cassert>
#include <iostream>
#include <vector>
#include <utility>
using Lines = std::array<unsigned,13>;
struct Flag {int p, l;};
Lines neighbors{};
std::vector<Flag> flags;
std::array<std::array<long long, 66>,5> counts{};
std::array<long long,5> isolated{};

bool augment(int p, unsigned& seen, std::array<int,13>& owner) {
    for (unsigned candidates=neighbors[p]&~seen; candidates; candidates&=candidates-1) {
        int l=__builtin_ctz(candidates);
        if(seen & (1u<<l)) continue;
        seen|=1u<<l;
        if(owner[l]<0 || augment(owner[l],seen,owner)) { owner[l]=p; return true; }
    }
    return false;
}
void enumerate(int start,int removed) {
    std::array<int,13> owner;
    owner.fill(-1);
    unsigned occupied=0;
    bool emptyPoint=false;
    int matching=0;
    for(int p=0;p<13;++p) {
        unsigned seen=0;
        matching+=augment(p,seen,owner);
        occupied|=neighbors[p];
        emptyPoint|=neighbors[p]==0;
    }
    bool emptyLine=occupied!=(1u<<13)-1;
    assert(matching==13-int(emptyPoint || emptyLine));
    ++counts[removed][52-removed+matching];
    isolated[removed]+=emptyPoint || emptyLine;
    if(removed==4) return;
    for(int k=start;k<int(flags.size());++k) {
        auto [p,l]=flags[k];
        neighbors[p]^=1u<<l;
        enumerate(k+1,removed+1);
        neighbors[p]^=1u<<l;
    }
}
int main() {
    for(int l=0;l<13;++l) for(int d:{0,1,3,9}) {
        int p=(l+d)%13; flags.push_back({p,l}); neighbors[p]|=1u<<l;
    }
    for(int p=0;p<13;++p) for(int q=0;q<p;++q)
        assert(__builtin_popcount(neighbors[p]&neighbors[q])==1);
    enumerate(0,0);
    for(int r=0;r<=4;++r) {
        std::cout<<"removed "<<r<<":";
        for(int cost=0;cost<=65;++cost) if(counts[r][cost])
            std::cout<<" cost "<<cost<<" in "<<counts[r][cost]<<" subsets;";
        std::cout<<" isolated point or line in "<<isolated[r]<<"\n";
    }
}
