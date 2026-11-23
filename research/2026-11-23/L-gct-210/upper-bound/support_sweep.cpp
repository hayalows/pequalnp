#include <array>
#include <cstdint>
#include <iostream>

constexpr int side = 5;
constexpr int rows = 11;
constexpr int prime = 1009;
int inverse[prime];
int hist[26][12];
int example[26][12][5];

void visit(std::array<int, 5> support) {
    int adj[rows][rows]{};
    int degrees[10]{};
    int m=0;
    for (int i=0; i<side; ++i) for (int j=0; j<side; ++j)
        if ((support[i]>>j)&1) {
            adj[i][side+j]=adj[side+j][i]=prime-1;
            ++degrees[i];
            ++degrees[side+j];
            ++m;
        }
    if (m==0) return;
    for (int i=0; i<rows-1; ++i) {
        adj[i][i]=(prime+1-degrees[i])%prime;
        adj[i][rows-1]=adj[rows-1][i]=(prime-degrees[i])%prime;
    }
    adj[rows-1][rows-1]=prime-m;
    int rank=0;
    for (int j=0; j<rows; ++j) {
        int pivot=rank;
        while (pivot<rows && !adj[pivot][j]) ++pivot;
        if (pivot==rows) continue;
        for (int col=j; col<rows; ++col) std::swap(adj[rank][col],adj[pivot][col]);
        for (int i=rank+1; i<rows; ++i) {
            const int c=prime-adj[i][j]*inverse[adj[rank][j]]%prime;
            for (int col=j; col<rows; ++col)
                adj[i][col]=(adj[i][col]+c*adj[rank][col])%prime;
        }
        ++rank;
    }
    const int nul=rows-rank;
    if (!hist[m][nul]) for (int i=0;i<5;++i) example[m][nul][i]=support[i];
    ++hist[m][nul];
    if ((m==18 || m==19) && nul>0) {
        std::cerr << m;
        for (int x:support) std::cerr << ' ' << x;
        std::cerr << '\n';
    }
}

int main() {
    inverse[1]=1;
    for (int i=2;i<prime;++i) inverse[i]=prime-prime/i*inverse[prime%i]%prime;
    for (int a=0;a<32;++a)
      for (int b=a;b<32;++b)
        for (int c=b;c<32;++c)
          for (int d=c;d<32;++d)
            for (int e=d;e<32;++e) visit({a,b,c,d,e});
    for (int m=1; m<=25; ++m) {
        int maxdim=0, maxnul=0;
        std::cout << "m=" << m << " counts (nullity:patterns)";
        for (int n=0;n<rows;++n) if (hist[m][n]) {
            maxdim=(m-1+n)/2;
            maxnul=n;
            std::cout << ' ' << n << ':' << hist[m][n];
        }
        std::cout << " d<=" << maxdim << " max-nullity row masks";
        for (int x: example[m][maxnul]) std::cout << ' ' << x;
        std::cout << '\n';
    }
}
