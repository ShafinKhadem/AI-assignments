//#undef DEBUG
#include <bits/stdc++.h>
using namespace std;
using ll = long long;
const ll llinf = (1ll<<61)-1;
const char lf = '\n', splf[] = " \n";
#define sz(a) int(a.size())
#define all(x) begin(x), end(x)
#define fi first
#define se second
#define r first
#define c second
#define Pair make_pair
const int inf = 1000000007;
int N;
using Var = pair<int, int>;
vector<Var> g[100][100];
using Arc = pair<Var, Var>;

class State {
public:
    bool fail;
    vector<vector<int> > grid;
    vector<vector<vector<int> > > dom;

    State() : fail(0) {}

    State(int sz) : fail(0), grid(sz, vector<int>(sz, 0)), dom(sz, vector<vector<int> >(sz, vector<int>())) {
        vector<int> d(sz);
        iota(all(d), 1);
        for (int i = 0; i < N; ++i) {
            for (int j = 0; j < N; ++j) {
                dom[i][j] = d;
            }
        }
    }

    void AC_3() {
        queue<Arc> q;
        for (int i = 0; i < N; ++i) {
            for (int j = 0; j < N; ++j) {
                for (Var &k: g[i][j]) {
                    q.push({{i, j}, k});
                }
            }
        }
        while (!q.empty()) {
            Arc a = q.front();
            q.pop();
            if (revise(a.fi, a.se)) {
                for (Var &k: g[a.fi.r][a.fi.c]) {
                    q.push({k, a.fi});
                }
            }
        }
    }

    bool revise(Var vi, Var vj) {
        auto &di = dom[vi.r][vi.c], &dj = dom[vj.r][vj.c];
        int szdj = sz(dj);
        if (szdj > 1) return 0;
        if (szdj == 0 and sz(di)) {
            di.clear();
            return 1;
        }
        auto it = find(all(di), dj[0]);
        if (it != di.end()) {
            di.erase(it);
            return 1;
        }
        return 0;
    }

    bool isValid() {
        for (int i = 0; i < N; ++i) {
            for (int j = 0; j < N; ++j) {
                if (!sz(dom[i][j])) return 0;
            }
        }
        return 1;
    }

    bool isComplete() {
        if (!isValid()) return 0;
        for (int i = 0; i < N; ++i) {
            for (int j = 0; j < N; ++j) {
                if (!grid[i][j]) return 0;
            }
        }
        return 1;
    }

    bool assign(Var x, int d) {
        auto &dx = dom[x.r][x.c];
        if (find(all(dx), d) == end(dx)) return 0;
        dx = {d};
        grid[x.r][x.c] = d;
        AC_3();
        return 1;
    }

    double impact(Var x, int d) {
        State after = *this;
        assert(after.assign(x, d));
        double p = 1;
        for (int i = 0; i < N; ++i) {
            for (int j = 0; j < N; ++j) {
                p *= sz(after.dom[i][j])*1.0/sz(dom[i][j]);
            }
        }
        return 1-p;
    }
};

Var SDF(State &csp) {
    Var var = {-1, -1};
    int mn = 1000;
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < N; ++j) {
            if (csp.grid[i][j]) continue;
            int cur = sz(csp.dom[i][j]);
            if (cur < mn) mn = cur, var = {i, j};
        }
    }
    assert(var.r != -1 and var.c != -1);
    return var;
}

Var brelaz(State &csp) {
    vector<int> cr(N, 0), cc(N, 0);
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < N; ++j) {
            if (csp.grid[i][j]) continue;
            ++cr[i], ++cc[j];
        }
    }
    Var var = {-1, -1};
    pair<int, int> mn = {1000, 1000};
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < N; ++j) {
            if (csp.grid[i][j]) continue;
            int fd = cr[i]+cc[j]-2;
            pair<int, int> cur = {sz(csp.dom[i][j]), -fd};
            if (cur < mn) mn = cur, var = {i, j};
        }
    }
    assert(var.r != -1 and var.c != -1);
    return var;
}

Var domddeg(State &csp) {
    vector<int> cr(N, 0), cc(N, 0);
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < N; ++j) {
            if (csp.grid[i][j]) continue;
            ++cr[i], ++cc[j];
        }
    }
    Var var = {-1, -1};
    double mn = 1000;
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < N; ++j) {
            if (csp.grid[i][j]) continue;
            int fd = cr[i]+cc[j]-2;
            double cur = fd ? sz(csp.dom[i][j])*1.0/fd : 999;
            if (cur < mn) mn = cur, var = {i, j};
        }
    }
    assert(var.r != -1 and var.c != -1);
    return var;
}

Var select_unassigned_variable(State &csp) {
    return SDF(csp);
}

State failure;
int cntNode, cntFail;

State BT_MAC(State csp) {
    ++cntNode;
    if (csp.isComplete()) return csp;
    if (!csp.isValid()) {
        ++cntFail;
        return failure;
    }
    Var var = select_unassigned_variable(csp);
    auto dv = csp.dom[var.r][var.c];
    sort(all(dv), [&](const int &l, const int &r) {
        return csp.impact(var, l) < csp.impact(var, r);
    });
    for (int &v: dv) {
        State ncsp = csp;
        ncsp.assign(var, v);
        State res = BT_MAC(ncsp);
        if (!res.fail) return res;
    }
    return failure;
}

int main() {
    failure.fail = 1;

    char gar;
    string bage;
    cin >> gar >> gar >> N >> gar >> bage >> bage;
    State init(N);

    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < N; ++j) {
            for (int k = j+1; k < N; ++k) {
                Var u = {i, j}, v = {i, k};
                g[u.r][u.c].push_back(v), g[v.r][v.c].push_back(u);
                u = {j, i}, v = {k, i};
                g[u.r][u.c].push_back(v), g[v.r][v.c].push_back(u);
            }
        }
    }

    for (int i = 0; i < N; ++i) {
        for (int j = 0, x; j < N; ++j) {
            cin >> x >> gar;
            if (x and !init.assign({i, j}, x)) {
                cout<<"Invalid\n";
                return 0;
            }
        }
    }

    State res = BT_MAC(init);
    cout << cntNode << ',' << cntFail << lf;
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < N; ++j) {
            cout << setw(2) << res.grid[i][j] << splf[j == N-1];
        }
    }
}
