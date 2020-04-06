//rerooting library by otera
template< typename U, typename T>
struct Rerooting {

    struct Edge {
        int to;
        U date;
        T dp;
    };

    using F1 = function< T(T, T) >;
    using F2 = function< T(T, U) >;

    vector<vector<Edge>> g;
    vector<T> dp, subdp;
    const T ident;
    const F1 f1;
    const F2 f2;

    Rerooting(int n, const F1 &f1, const F2 &f2, const T &ident) : g(n), f1(f1), f2(f2), dp(n, ident), subdp(n, ident), ident(ident) {}

    void add_edge(int s, int t, const U &d) {
        g[s].emplace_back((Edge) {t, d, ident});
        g[t].emplace_back((Edge) {s, d, ident});
    }

    void add_edge_bi(int s, int t, const U &d, const U &e) {
        g[s].emplace_back((Edge) {t, d, ident});
        g[t].emplace_back((Edge) {s, e, ident});
    }

    void rec(int v, int par) {
        for(auto &e: g[v]) {
            if(e.to == par) continue;
            rec(e.to, v);
            subdp[v] = f1(subdp[v], f2(subdp[e.to], e.date));
        }
    }

    void rerec(int v, int par, const T &pval) {
        int sz = (int)g[v].size();
        vector<T> left(sz + 1, ident), right(sz + 1, ident);
        for(int i = 0; i < sz; ++ i) {
            auto &e = g[v][i];
            e.dp = f2(par == e.to ? pval : subdp[e.to], e.date);
            left[i + 1] = f1(left[i], e.dp);
        }
        dp[v] = left[sz];
        for(int i = 0; i < sz; ++ i) {
            auto &e = g[v][sz - 1 - i];
            if(e.to != par) {
                rerec(e.to, v, f1(left[sz - 1 - i], right[i]));
            }
            right[i + 1] =  f1(right[i], e.dp);
        }
    }

    vector<T> build() {
        rec(0, -1);
        rerec(0, -1, ident);
        return dp;
    }
};

//verify 
//ABC160F

#include<iostream>
#include<string>
#include<cstdio>
#include<cstring>
#include<vector>
#include<cmath>
#include<algorithm>
#include<functional>
#include<iomanip>
#include<queue>
#include<deque>
#include<ciso646>
#include<random>
#include<map>
#include<set>
#include<complex>
#include<bitset>
#include<stack>
#include<unordered_map>
#include<utility>
#include<cassert>
using namespace std;
 
//#define int long long
typedef long long ll;
typedef unsigned long long ul;
typedef unsigned int ui;
typedef long double ld;
const int inf=1e9+7;
const ll INF=1LL<<60 ;
const ll mod=1e9+7 ;
#define rep(i,n) for(int i=0;i<n;i++)
#define per(i,n) for(int i=n-1;i>=0;i--)
#define Rep(i,sta,n) for(int i=sta;i<n;i++)
#define rep1(i,n) for(int i=1;i<=n;i++)
#define per1(i,n) for(int i=n;i>=1;i--)
#define Rep1(i,sta,n) for(int i=sta;i<=n;i++)
typedef complex<ld> Point;
const ld eps = 1e-8;
const ld pi = acos(-1.0);
typedef pair<int, int> P;
typedef pair<ld, ld> LDP;
typedef pair<ll, ll> LP;
#define fr first
#define sc second
#define all(c) c.begin(),c.end()
#define pb push_back
#define debug(x)  cerr << #x << " = " << (x) << endl;
template<class T> inline bool chmax(T& a, T b) { if (a < b) { a = b; return 1; } return 0; }
template<class T> inline bool chmin(T& a, T b) { if (a > b) { a = b; return 1; } return 0; }
 
template<int MOD> struct Fp {
    long long val;
    constexpr Fp(long long v = 0) noexcept : val(v % MOD) {
        if (val < 0) val += MOD;
    }
    constexpr int getmod() { return MOD; }
    constexpr Fp operator - () const noexcept {
        return val ? MOD - val : 0;
    }
    constexpr Fp operator + (const Fp& r) const noexcept { return Fp(*this) += r; }
    constexpr Fp operator - (const Fp& r) const noexcept { return Fp(*this) -= r; }
    constexpr Fp operator * (const Fp& r) const noexcept { return Fp(*this) *= r; }
    constexpr Fp operator / (const Fp& r) const noexcept { return Fp(*this) /= r; }
    constexpr Fp& operator += (const Fp& r) noexcept {
        val += r.val;
        if (val >= MOD) val -= MOD;
        return *this;
    }
    constexpr Fp& operator -= (const Fp& r) noexcept {
        val -= r.val;
        if (val < 0) val += MOD;
        return *this;
    }
    constexpr Fp& operator *= (const Fp& r) noexcept {
        val = val * r.val % MOD;
        return *this;
    }
    constexpr Fp& operator /= (const Fp& r) noexcept {
        long long a = r.val, b = MOD, u = 1, v = 0;
        while (b) {
            long long t = a / b;
            a -= t * b; swap(a, b);
            u -= t * v; swap(u, v);
        }
        val = val * u % MOD;
        if (val < 0) val += MOD;
        return *this;
    }
    constexpr bool operator == (const Fp& r) const noexcept {
        return this->val == r.val;
    }
    constexpr bool operator != (const Fp& r) const noexcept {
        return this->val != r.val;
    }
    friend constexpr ostream& operator << (ostream &os, const Fp<MOD>& x) noexcept {
        return os << x.val;
    }
    friend constexpr istream& operator >> (istream &is, Fp<MOD>& x) noexcept {
        return is >> x.val;
    }
    friend constexpr Fp<MOD> modpow(const Fp<MOD> &a, long long n) noexcept {
        if (n == 0) return 1;
        auto t = modpow(a, n / 2);
        t = t * t;
        if (n & 1) t = t * a;
        return t;
    }
};

template<class T> struct BiCoef {
    vector<T> fact_, inv_, finv_;
    constexpr BiCoef() {}
    constexpr BiCoef(int n) noexcept : fact_(n, 1), inv_(n, 1), finv_(n, 1) {
        init(n);
    }
    constexpr void init(int n) noexcept {
        fact_.assign(n, 1), inv_.assign(n, 1), finv_.assign(n, 1);
        int MOD = fact_[0].getmod();
        for(int i = 2; i < n; i++){
            fact_[i] = fact_[i-1] * i;
            inv_[i] = -inv_[MOD%i] * (MOD/i);
            finv_[i] = finv_[i-1] * inv_[i];
        }
    }
    constexpr T com(int n, int k) const noexcept {
        if (n < k || n < 0 || k < 0) return 0;
        return fact_[n] * finv_[k] * finv_[n-k];
    }
    constexpr T fact(int n) const noexcept {
        if (n < 0) return 0;
        return fact_[n];
    }
    constexpr T inv(int n) const noexcept {
        if (n < 0) return 0;
        return inv_[n];
    }
    constexpr T finv(int n) const noexcept {
        if (n < 0) return 0;
        return finv_[n];
    }
};
 
const int MOD = 1000000007;
using mint = Fp<MOD>;
BiCoef<mint> bc;
 
void solve() {
    using pmi = pair<mint, int>;
	int n; cin >> n;

    auto f1 = [](pmi a, pmi b) {
        return pmi(a.fr * b.fr * bc.com(a.sc + b.sc, a.sc), a.sc + b.sc);
    };

    auto f2 = [](pmi a, int b) {
        return pmi(a.fr, a.sc + b);
    };

    Rerooting<int, pmi> rerooting(n, f1, f2, pmi((mint)1, 0));
    rep(i, n - 1) {
        int a, b; cin >> a >> b;
        --a, --b;
        rerooting.add_edge(a, b, 1);
    }
    bc.init(600600);
    for(auto p: rerooting.build()) {
        cout << p.fr << endl;
    }
}
 
signed main() {
	ios::sync_with_stdio(false);
	cin.tie(0);
	//cout << fixed << setprecision(10);
	//int t; cin >> t; rep(i, t)solve();
	solve();
    return 0;
}

