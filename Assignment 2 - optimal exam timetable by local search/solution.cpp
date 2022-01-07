//#undef DEBUG
#include <bits/stdc++.h>
using namespace std;
using ll = long long;
const ll llinf = (1ll<<61)-1;
const char lf = '\n', splf[] = " \n";
#define sz(a) int(a.size())
#define all(x) begin(x), end(x)
#define TCC template<class C
#define OSO ostream &operator<<(ostream &os, const
#ifdef DEBUG
const int DEBUG_END = 26;
#define DOS cout
#include <debug.h>
#else
#define bug(args...) void()
#define cbug(a, args...)
#endif
#define ASSERT(a, o, b, args...) if (!((a)o(b))) bug(a, b, ##args), assert((a)o(b));
#define fi first
#define se second
#define Pair make_pair

struct Table{
    vector<int> widths;
    int curCol = 0, nxtWidth = 1, cntCol, totalWidth;
    Table(vector<int> _widths): widths(_widths), cntCol(sz(widths)), totalWidth(accumulate(all(widths),1+cntCol)) {}
    void hr(bool special = 0) {
        if (special) cout<<'+'<<string(totalWidth-2,'-')<<"+\n";
        else cout<<'-'<<string(totalWidth-2,'-')<<"-\n";
        curCol = 0;
    }
    void setNxtWidth(int _nxtWidth) {nxtWidth = _nxtWidth;}
    TCC> Table& operator<<(C x) {
        if(!curCol)cout<<'|';
        cout<<setw(accumulate(begin(widths)+curCol,begin(widths)+curCol+nxtWidth,nxtWidth-1))<<left<<x<<'|';
        if((curCol+=nxtWidth)==cntCol)curCol=0,cout<<'\n';
        nxtWidth=1;
        return *this;
    }
};


const int N=1005,S=50005;
vector<int> g[N], courses[S];
int n,s,adj[N][N],deg[N];

void assignGrundyColor(int i, vector<int> &color){
    assert(i>=1 and i<=n and color[i]==-1);
    bitset<N> adjColor;
    for(int &j: g[i]) if(color[j]>=0) adjColor[color[j]]=1;
    color[i]=0;
    while(adjColor[color[i]])++color[i];
}

vector<int> colorInOrder(vector<int> order){
    vector<int> color(n+1,-1);
    for(int &i: order) assignGrundyColor(i, color);
    return color;
}

vector<int> LDOColor(){
    vector<int>order;
    {
        int mxDeg=*max_element(deg+1,deg+1+n);
        vector<vector<int>>tmp(mxDeg+1);
        for(int i=1;i<=n;++i)tmp[deg[i]].push_back(i);
        for(int i=mxDeg;i>=0;--i) for(int &j: tmp[i]) order.push_back(j);
    }
    return colorInOrder(order);
}

vector<int> DSatur(){
    bitset<N> adjCol[N];
    vector<int> color(n+1,-1),degSatur(n+1);
    for(int iter=0;iter<n;++iter){
        int i=-1;
        pair<int,int>mx={-1,-1};
        for(int j=1;j<=n;++j){
            auto tmp=Pair(degSatur[j],deg[j]);
            if(color[j]==-1 and tmp>mx)mx=tmp,i=j;
        }
        assignGrundyColor(i,color);
        for(int &j: g[i]) if(!adjCol[j][color[i]]) adjCol[j][color[i]]=1,++degSatur[j];
    }
    return color;
}

int penalty(vector<int> color){
    int penalty=0;
    for(int i=1;i<=n;++i){
        assert(color[i]>=0);
        for(int &j: g[i]){
            int c1=color[i],c2=color[j];
            assert(c1!=c2);
            penalty+=(c2>c1 and c2-c1<=5) ? adj[i][j]*(32>>(c2-c1)): 0;
        }
    }
    return penalty;
}

vector<int> SWO(vector<int> color){
    pair<int,int> ctsp={*max_element(all(color)),penalty(color)};
    while(1){
        vector<int>order;
        {
            vector<vector<int>>tmp(ctsp.fi+1);
            for(int i=1;i<=n;++i)tmp[color[i]].push_back(i);
            for(int i=ctsp.fi;i>=0;--i) for(int &j: tmp[i]) order.push_back(j);
        }
        auto nc=colorInOrder(order);
        pair<int,int> ntsp={*max_element(all(nc)),penalty(nc)};
        if(ctsp>ntsp)ctsp=ntsp,color=nc;
        else break;
    }
    return color;
}

vector<int> pairSwap(vector<int> color){
    const int minDec=s/2;
    while(1){
        int cp=penalty(color),ip=cp;
        array<int,N> adjColor[N];
        for(int i=1;i<=n;++i) {
            fill(all(adjColor[i]),0);
            for(int &j: g[i]) ++adjColor[i][color[j]];
        }
        for(int i=1;i<=n;++i){
            for(int j=i+1;j<=n;++j){
                if(color[i]==color[j] or adjColor[i][color[j]] or adjColor[j][color[i]])continue;
                vector<int>nc=color;
                swap(nc[i],nc[j]);
                int np = penalty(nc);
                if(np<cp){
                    for(int &k: g[i]) --adjColor[k][color[i]];
                    for(int &k: g[j]) --adjColor[k][color[j]];
                    cp=np,swap(color[i],color[j]);
                    for(int &k: g[i]) ++adjColor[k][color[i]];
                    for(int &k: g[j]) ++adjColor[k][color[j]];
                }
            }
        }
        if(ip-cp<minDec)break;
    }
    return color;
}

vector<int> kempeSwap(vector<int> color){
    const int minDec=s/2;
    while(1){
        int cp=penalty(color), ip=cp;
        bitset<N> vstd[N];
        for(int v=1;v<=n;++v) for(int &u: g[v]) if(!vstd[v][u] and !vstd[u][v]){
            vector<int>nc=color;
            bitset<N> curVstd;
            curVstd[v]=1;
            queue<int>q;
            q.push(v);
            while(!q.empty()){
                int nod=q.front();
                nc[nod]^=color[u]^color[v];
                q.pop();
                for(int &adjnod: g[nod]) if(!curVstd[adjnod] and (color[adjnod]==color[v] or color[adjnod]==color[u])){
                    vstd[nod][adjnod]=1,curVstd[adjnod]=1,q.push(adjnod);
                }
            }
            int np=penalty(nc);
            if(np<cp)cp=np,color=nc;
        }
        if(ip-cp<minDec)break;
    }
    return color;
}

function<vector<int>()> scheme[4] = {
    {[](){
        auto color=DSatur();
        color=SWO(color);
        color=kempeSwap(color);
        color=pairSwap(color);
        return color;
    }},
    {[](){
        auto color=DSatur();
        color=kempeSwap(color);
        color=pairSwap(color);
        return color;
    }},
    {[](){
        auto color=LDOColor();
        color=SWO(color);
        color=kempeSwap(color);
        color=pairSwap(color);
        return color;
    }},
    {[](){
        auto color=LDOColor();
        color=kempeSwap(color);
        color=pairSwap(color);
        return color;
    }}
};


signed main(int argc, char** argv) {
    if(argc < 2) {
		cerr << "Please run this as: ./<program> <test name>\n";
		return 0;
	}
    string test=argv[1];
    //vector<int> optimalColor;
    {
        ifstream crs, stu/*, sol*/;
        try {
            crs.open(test+".crs");
            stu.open(test+".stu");
            //sol.open(test+".sol");
        } catch (exception& e) {
            cerr << "Exception: " << e.what() << "\n";
            return 1;
        }
        string line;
        while(getline(crs,line))++n;
        assert(n<N and s==0);
        while(getline(stu,line)){
            ++s;
            ASSERT(s,<,S);
            int c;
            istringstream iss(line);
            auto &v=courses[s];
            while(iss>>c) v.push_back(c);
            for(int &i: v) for(int &j: v) if (i!=j) ++adj[i][j];
        }
        /*optimalColor.resize(n+1,-1);
        int c,ts;
        while(sol>>c>>ts){
            optimalColor[c]=ts;
        }*/
        crs.close();
        stu.close();
        //sol.close();
    }
    for(int i=1;i<=n;++i){
        for(int j=1;j<=n;++j)if(adj[i][j])g[i].push_back(j);
    }
    for(int i=1;i<=n;++i){
        for(int j=1;j<=n;++j)deg[i]+=bool(adj[i][j]);
    }
    cout<<"test "<<test<<lf;
    //cout<<"optimal: timeslots "<<*max_element(all(optimalColor))+1<<' '<<"penalty "<<penalty(optimalColor)/double(s)<<lf;
    //Table table({10,10,10,10,10,10,10,10});
    for(int i=0;i<4;++i){
        auto color=scheme[i]();
        cout<<"scheme "<<i+1<<lf;
        cout<<"timeslots "<<*max_element(all(color))+1<<' '<<"penalty "<<penalty(color)/double(s)<<lf;
        //table<<*max_element(all(color))+1<<penalty(color)/double(s);
    }
    //table.hr();
    /*{
        auto color=scheme[3]();
        ofstream sol("1605045.sol");
        for(int i=1;i<=n;++i)sol<<setw(4)<<i<<' '<<color[i]<<lf;
        sol.close();
    }*/
}
