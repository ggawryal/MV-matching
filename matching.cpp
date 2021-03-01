#include<bits/stdc++.h>
using namespace std;
#ifdef DEBUG
int D_RECUR_DEPTH = 0;
#define deb(x) {++D_RECUR_DEPTH; auto x2=x; --D_RECUR_DEPTH; cerr<<string(D_RECUR_DEPTH, '\t')<<"\e[91m"<<__func__<<":"<<__LINE__<<"\t"<<#x<<" = "<<x2<<"\e[39m"<<endl;}
template<typename O, typename C> typename enable_if<is_same<O,ostream>::value, O&>::type operator<<(O& ost,  const C& v){if(&ost == &cout) {cerr<<"Warning, printing debugs on cout!"<<endl;} ost<<"["; bool firstIter = true; for(auto& x:v){ if(firstIter) firstIter = false; else ost<<", "; ost<<x;} return ost<<"]";}
template<typename Ostream, typename ...Ts>Ostream& operator<<(Ostream& ost,  const pair<Ts...>& p){if(&ost == &cout) {cerr<<"Warning, printing debugs [pair] on cout!"<<endl;}return ost<<"{"<<p.first<<", "<<p.second<<"}";}
#else
#define deb(x)
#endif

template<class C> C reversed(C c) {reverse(c.begin(),c.end()); return c;}
#define mp make_pair
#define st first
#define nd second
typedef long long ll;
typedef pair<int,int> pii;


struct DSU {
    vector<int> link;
    void reset(int n) {
        link = vector<int>(n);
        iota(link.begin(), link.end(), 0);
    }
    
    int find(int a) {
        return link[a] = (a == link[a] ? a : find(link[a]));
    }

    int operator[](const int& a) {
        return find(a);
    }

    void linkTo(int a, int b) {
        link[find(a)] = find(b);
    }

};

enum EdgeType {NotScanned, Prop, Bridge};
struct Edge {
    int from,to;
    int other;
    bool matched;
    EdgeType type = NotScanned;
};

const int INF = 1e9;

int n;
vector<vector<Edge> > graph;
vector<vector<int> > predecessors;
vector<int> evenlvl, oddlvl;
DSU bud;
enum Color {None, Red, Green};
vector<Color> color;
vector<int> parentInDDFSTree;
vector<Edge> myBridge;


int minlvl(int u) { return min(evenlvl[u], oddlvl[u]); }
int maxlvl(int u) { return max(evenlvl[u], oddlvl[u]); }
void setLvl(int u, int i) { if(i&1) oddlvl[u] = i; else evenlvl[u] = i;}

int tenacity(Edge e) {
    if(e.matched)
        return oddlvl[e.from] + oddlvl[e.to] + 1;
    return evenlvl[e.from] + evenlvl[e.to] + 1;
}

/*
tries to move color1 down, updating colors, stacks and parents in ddfs tree
also adds each visited vertex  to support of this bridge
terminates either when:
    (*) found reachable vertex in lower layer (possibly after backtracking from this color dfs)
    (*) found bottleneck
    (*) backtracked whole stack and recolored other color's center of activity since no other path not visiting this vertex found
*/
int ddfsMove(vector<int>& stack1, const Color color1, vector<int>& stack2, const Color color2, vector<int>& support) {
    int alternativeParent = -1;
    while(stack1.size() > 0) {
        int u = stack1.back();
        bool foundChild = false;
        for(auto a: predecessors[u]) {
            int v = bud[a];
            if(color[v] == None) {
                stack1.push_back(v);
                support.push_back(v);
                parentInDDFSTree[v] = u;
                color[v] = color1;
                foundChild = true;
                break;
            }
            else if(v == stack2.back()) {
                alternativeParent = u;
            }
        }
        if(!foundChild)
            stack1.pop_back();
        else if(minlvl(stack1.back()) <= minlvl(stack2.back())) //should be ok in both cases: when color1 == Red and when color1 == Green
            return -1;
    }

    if(stack1.size() == 0) {
        if(stack2.size() <= 1) {
            //found bottleneck
            assert(stack2.size() == 1);
            color[stack2.back()] = None;
            parentInDDFSTree[stack2.back()] = -1;
            return stack2.back();
        }
        //change colors
        stack1.push_back(stack2.back());
        assert(color[stack2.back()] == color2);
        color[stack2.back()] = color1;
        assert(alternativeParent != -1);
        parentInDDFSTree[stack2.back()] = alternativeParent;
        stack2.pop_back();
    }
    return -1;
}

//returns {r0, g0} or {bottleneck, bottleneck}
pair<int,int > ddfs(Edge e, vector<int>& out_support) {
    assert(e.type == Bridge);
    vector<int> Sr = {bud[e.from]}, Sg = {bud[e.to]};
    if(Sr[0] == Sg[0]) {
        out_support = {};
        return {Sr[0],Sg[0]};
    }
    out_support = {Sr[0], Sg[0]};
    color[Sr[0]] = Red;
    color[Sg[0]] = Green;

    for(;;) {
        deb(Sr);
        deb(Sg);

        //if found two disjoint paths
        if(minlvl(Sr.back()) == 0 && minlvl(Sg.back()) == 0) {
            out_support.clear();
            return {Sr.back(),Sg.back()};
        }
    
        int b;
        if(minlvl(Sr.back()) >= minlvl(Sg.back()))
            b = ddfsMove(Sr,Red,Sg,Green, out_support);
        else
            b = ddfsMove(Sg,Green,Sr,Red, out_support);
        if(b != -1) {
            out_support.erase(remove(out_support.begin(),out_support.end(),b),out_support.end());
            return {b,b};
        }
    }
    exit(1);
}

bool isVertexMatched(int u) {
    for(auto e:graph[u])
        if(e.matched)
            return true;
    return false;
}

void bfs() {
    vector<vector<int> > verticesAtLevel(n);
    vector<vector<Edge> > bridges(2*n+2);

    for(int u=0;u<n;u++)
        if(!isVertexMatched(u)) {
            verticesAtLevel[0].push_back(u);
            setLvl(u,0);
        }
            
    for(int i=0;i<n;i++) {
        cerr<<"phase "<<i<<endl;
        for(auto u : verticesAtLevel[i]) {
            cerr<<"["<<u<<"]"<<endl;
            for(auto& e:graph[u]) {
                if(e.type == NotScanned && ((oddlvl[u] == i && e.matched) || (evenlvl[u] == i && !e.matched))) {
                    if(minlvl(e.to) >= i+1) {
                        e.type = Prop;
                        graph[e.to][e.other].type = Prop;

                        if(minlvl(e.to) > i+1) {
                            setLvl(e.to,i+1);
                            verticesAtLevel[i+1].push_back(e.to);
                        }
                        predecessors[e.to].push_back(u);
                    }
                    else {
                        cerr<<"new bridge "<<e.from<<" "<<e.to<<endl;
                        e.type = Bridge;
                        graph[e.to][e.other].type = Bridge;
                        if(tenacity(e) < INF) {
                            cerr<<"found bridge "<<e.from<<" "<<e.to<<" tenacity "<<tenacity(e)<<endl;
                            bridges[tenacity(e)].push_back(e);
                        }
                    }
                }
            }
        }
        

        for(auto e : bridges[2*i+1]) {
            vector<int> support;
            pair<int,int> ddfsResult = ddfs(e,support);
            if(ddfsResult.first == ddfsResult.second) {
                cerr<<"found bottleneck "<<ddfsResult.first<<endl;
                deb(support);
                for(auto v:support) {
                    setLvl(v,2*i+1-minlvl(v));
                    verticesAtLevel[2*i+1-minlvl(v)].push_back(v);
                    myBridge[v] = e;
                    bud.linkTo(v,ddfsResult.first);
                    cerr<<v<<" -> "<<bud[v]<<endl;

                    if(evenlvl[v] > oddlvl[v]) {
                        for(auto f : graph[v]) {
                            if(f.type == Bridge && tenacity(f) < INF && ((f.matched && oddlvl[v] == maxlvl(v)) || (!f.matched && evenlvl[v] == maxlvl(v)))) {
                                cerr<<"max found tenacity of new bridge "<<f.from<<" "<<f.to<<endl;
                                assert(f.type == Bridge);
                                bridges[tenacity(f)].push_back(f);
                            }
                        }
                    }
                }
            }
            else {
                cerr<<"augumenting path found, from "<<ddfsResult.first<<" to "<<ddfsResult.second<<endl;
                //TODO
                exit(0);
            }
        }
        for(int j=0;j<n;j++) {
            if(minlvl(j) < INF)
                cerr<<minlvl(j)<<" ";
            else
                cerr<<"X ";
        }
        cerr<<endl;
        for(int j=0;j<n;j++) {
            if(maxlvl(j) < INF)
                cerr<<maxlvl(j)<<" ";
            else
                cerr<<"O ";
        }
        cerr<<endl;
    }
}

int32_t main(){
    ios::sync_with_stdio(false);
    int m,a,b;
    cin >> n >> m;
    graph.resize(n);
    predecessors.resize(n);
    evenlvl.resize(n,INF);
    oddlvl.resize(n,INF);


    bud.reset(n);
    color.resize(n,None);
    parentInDDFSTree.resize(n,-1);
    myBridge.resize(n,{-1,-1,-1,false,NotScanned});

    for(int i=0;i<m;i++) {
        int isMatched;
        cin >> a >> b >> isMatched;
        graph[a].push_back({a, b, (int)graph[b].size(), isMatched, NotScanned});
        graph[b].push_back({b, a, (int)graph[a].size()-1,isMatched, NotScanned});
    }
    bfs();
}
