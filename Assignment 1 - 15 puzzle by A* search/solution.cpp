#include <bits/stdc++.h>
using namespace std;
using ll = long long; using ull = unsigned long long; using ld = long double;
int T, cn;

void stateIn(vector<vector<int>> &v) {
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            cin >> v[i][j];
        }
    }
}

void stateOut(vector<vector<int>> &v) {
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            cout << setfill('0') << setw(2) << v[i][j] << " \n"[j==3];
        }
    }
}

string stateToString(const vector<vector<int>> &v) {
    string ret(16, 'a');
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            ret[i*4+j] = char(v[i][j]);
        }
    }
    return ret;
}

::vector<vector<int>> stringToState(string state) {
    vector<vector<int> > v(4, vector<int>(4));
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            v[i][j] = state[i*4+j];
        }
    }
    return v;
}


::pair<int, int> getBlank(const vector<vector<int>> &cur) {
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            if (!cur[i][j]) return make_pair(i, j);
        }
    }
    return {-1, -1};
}


int invCnt(string state) {
    int ret = 0;
    for (int i = 0; i < 16; i++) {
        if (!state[i]) continue;
        for (int j = i+1; j <= 15; j++) {
            ret += state[j] and state[i]>state[j];
        }
    }
    return ret;
}

bool checkSolvability(vector<vector<int>> init, const vector<vector<int>> &goal) {
    int bc, cnt = 0;
    vector<int> revp(17);
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            if (goal[i][j]) revp[goal[i][j]] = ++cnt;
            else bc = i;
        }
    }
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            init[i][j] = revp[init[i][j]];
        }
    }
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            if (!init[i][j]) return ((abs(bc-i)+1)&1)^(invCnt(stateToString(init))&1);
        }
    }
    return 0;
}

struct Misplacement
{
    int operator()(const vector<vector<int>> &cur, const vector<vector<int>> &goal) {
        int ret = 0;
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 4; j++) {
                ret += cur[i][j] and cur[i][j]!=goal[i][j];
            }
        }
        return ret;
    }

    friend ostream& operator <<(ostream &os, const Misplacement &rs) {
        return os << "Misplacement";
    }
};

struct Manhattan
{
    int operator()(const vector<vector<int>> &cur, const vector<vector<int>> &goal) {
        vector<pair<int, int> > pos(17);
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 4; j++) {
                pos[goal[i][j]] = {i, j};
            }
        }
        int ret = 0;
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 4; j++) {
                ret += cur[i][j] ? abs(pos[cur[i][j]].first-i)+abs(pos[cur[i][j]].second-j) : 0;
            }
        }
        return ret;
    }

    friend ostream& operator <<(ostream &os, const Manhattan &rs) {
        return os << "Manhattan";
    }
};


int dirr[] = {-1, 0, 1, 0}, dirc[] = {0, -1, 0, 1};
char dir[] = "ULDR", revDir[] = "DRUL";

vector<vector<int>> moveToDir(vector<vector<int>> &cur, char d) {
    int r, c;
    tie(r, c) = getBlank(cur);
    vector<vector<int> > ret = cur;
    for (int i = 0; i < 4; i++) {
        if (dir[i]!=d) continue;
        int nr = r+dirr[i], nc = c+dirc[i];
        if (nr>=0 and nr<4 and nc>=0 and nc<4) swap(ret[r][c], ret[nr][nc]);
    }
    return ret;
}

template<class C> void aStar(vector<vector<int>> init, vector<vector<int>> goal, C heuristic) {
    priority_queue<pair<int, string>, vector<pair<int, string> >, greater<pair<int, string> > > pq;
    map<string, int> g;
    map<string, char> p;

    auto start = chrono::high_resolution_clock::now();

    string os = stateToString(init);
    g[os] = 0, pq.push({heuristic(init, goal), os});
    int cnt = 1;

    while (1) {
        auto tmp = pq.top();
        pq.pop();
        auto cur = stringToState(tmp.second);
        if (cur==goal) break;
        int curg = g[tmp.second];
        if (curg+heuristic(cur, goal)<tmp.first) continue;

        for (int i = 0; i < 4; i++) {
            auto nxt = moveToDir(cur, dir[i]);
            if (nxt==cur) continue;
            string ns = stateToString(nxt);
            if (!g.count(ns) or curg+1<g[ns]) {
                g[ns] = curg+1, p[ns] = char(i), cnt++;
                pq.push(make_pair(g[ns]+heuristic(nxt, goal), ns));
            }
        }
    }

    auto stop = chrono::high_resolution_clock::now();
    auto duration = chrono::duration_cast<chrono::microseconds>(stop - start);

    auto tmp = goal;
    stack<string> path;
    string moves;
    while (1) {
        auto o = stateToString(tmp);
        path.push(o);
        if (tmp==init) break;
        int pd = p[o];
        moves.push_back(dir[pd]);
        tmp = moveToDir(tmp, revDir[pd]);
    }

    reverse(begin(moves), end(moves));
    cout << "\n----------- " << heuristic << " -----------\n\n";
    cout << "Cost\t\t\t" << moves.size() << '\n';
    cout << "Node expanded\t" << cnt << "\nMoves\t\t\t" << moves << '\n';

    /*cout.imbue(locale(""));
    cout << "Time taken\t\t" << duration.count() << " microseconds" << '\n';
    cout.imbue(locale("C"));*/
    /*while (!path.empty()) {
        auto o = stringToState(path.top());
        path.pop();
        stateOut(o);
        cout << '\n';
    }*/
}

signed main() {
    freopen("in.txt", "r", stdin);
    cin >> T;
    T--;
    vector<vector<int> > goal(4, vector<int>(4));
    stateIn(goal);
    while (cn++!=T) {
        cout << "---------------\nCase " << cn << "\n---------------\n";
        vector<vector<int> > init(4, vector<int>(4));
        stateIn(init);
        if (!checkSolvability(init, goal)) {
            cout << "\nNot solvable\n";
            goto eot;
        }
        aStar(init, goal, Manhattan());
        aStar(init, goal, Misplacement());

        eot: cout << "\n\n";
    }
}