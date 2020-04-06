//rerooting library by otera
template< typename Date, typename T>
struct Rerooting {

    struct Edge {
        int to;
        Date date;
        T dp;
    };

    using F1 = function< T(T, T) >;
    using F2 = function< T(T, Date) >;

    vector<vector<Edge>> g;
    vector<T> dp, subdp;
    const T ident;
    const F1 f1;
    const F2 f2;

    Rerooting(int n, const F1 &f1, const F2 &f2, const T &ident) : g(n), f1(f1), f2(f2), dp(n, ident), subdp(n, ident) {}

    void add_edge(int s, int t, const Date &d) {
        g[s].emplace_back((Edge) {t, d, ident});
        g[t].emplace_back((Edge) {s, d, ident});
    }

    void add_edge_bi(int s, int t, const Date &d, const Date &e) {
        g[s].emplace_back((Edge) {t, d, ident, ident});
        g[t].emplace_back((Edge) {s, e, ident, ident});
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