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
    vector<int> directParent;
    void reset(int n) {
        link = vector<int>(n);
        iota(link.begin(), link.end(), 0);
        directParent = vector<int>(n,-1);
    }
    
    int find(int a) {
        return link[a] = (a == link[a] ? a : find(link[a]));
    }

    int operator[](const int& a) {
        return find(a);
    }

    void linkTo(int a, int b) {
        assert(directParent[a] == -1);
        assert(directParent[b] == -1);
        link[find(a)] = find(b);
        directParent[a] = b;
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
vector<int> ddfsPredecessorsPtr;
vector<int> removed;
vector<int> evenlvl, oddlvl;
DSU bud;

int globalColorCounter; //reset to 1
//colors for bridges are numbered (2,3), (4,5), (6,7) ...
//to check if vertices belong to same petal check if color1/2 == color2/2
//color^1 is the other color for single ddfs run

vector<int> color;
vector<vector<int> > childsInDDFSTree; //may also contain other color vertices which previously were its childs

vector<Edge> myBridge;
vector<pair<int,int> > myBudBridge; //bud[bridge]


int minlvl(int u) { return min(evenlvl[u], oddlvl[u]); }
int maxlvl(int u) { return max(evenlvl[u], oddlvl[u]); }
void setLvl(int u, int i) { if(i&1) oddlvl[u] = i; else evenlvl[u] = i;}

int tenacity(Edge e) {
    if(e.matched)
        return oddlvl[e.from] + oddlvl[e.to] + 1;
    return evenlvl[e.from] + evenlvl[e.to] + 1;
}

/*
tries to move color1 down, updating colors, stacks and childs in ddfs tree
also adds each visited vertex to support of this bridge
*/
int ddfsMove(vector<int>& stack1, const int color1, vector<int>& stack2, const int color2, vector<int>& support) {
    int u = stack1.back();
    for(; ddfsPredecessorsPtr[u] < predecessors[u].size(); ddfsPredecessorsPtr[u]++) { //speedup
        int a = predecessors[u][ddfsPredecessorsPtr[u]];
        int v = bud[a];
        assert(removed[a] == removed[v]);
        if(removed[a])
            continue;
        if(color[v] == 0) {
            stack1.push_back(v);
            support.push_back(v);
            childsInDDFSTree[u].push_back(v);
            color[v] = color1;
            return -1;
        }
        else if(v == stack2.back())
            childsInDDFSTree[u].push_back(v);
    }
    stack1.pop_back();

    if(stack1.size() == 0) {
        if(stack2.size() == 1) { //found bottleneck
            color[stack2.back()] = 0;
            return stack2.back();
        }
        //change colors
        assert(color[stack2.back()] == color2);
        stack1.push_back(stack2.back());
        color[stack1.back()] = color1;
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
    int newRed = ++globalColorCounter;
    int newGreen = ++globalColorCounter;
    assert(newRed == (newGreen^1));
    color[Sr[0]] = newRed;
    color[Sg[0]] = newGreen;

    for(;;) {
        //if found two disjoint paths
        if(minlvl(Sr.back()) == 0 && minlvl(Sg.back()) == 0) {
            out_support.clear();
            return {Sr.back(),Sg.back()};
        }
    
        int b;
        if(minlvl(Sr.back()) >= minlvl(Sg.back()))
            b = ddfsMove(Sr,newRed,Sg, newGreen, out_support);
        else
            b = ddfsMove(Sg,newGreen,Sr, newRed, out_support);
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

bool openingDfs(int cur, int b,vector<int>& outPath) {
    if(cur == b)
        return true;
    outPath.push_back(cur);
    for(auto a: childsInDDFSTree[cur]) { 
        if(a == b || (color[a] == color[cur] && !removed[a] && openingDfs(a,b,outPath)))
            return true;
    }
    outPath.pop_back();
    return false;
}

void concat(vector<int>& a, const vector<int>& b) {
    for(auto x : b)
        a.push_back(x);
}

vector<int> openEdge(int u, int v);

vector<int> openPath(vector<int> p, bool saveLast = false) {
    vector<int> res;
    for(int i=0;i+1<p.size();i++)
        concat(res,openEdge(p[i],p[i+1]));
    if(saveLast && p.size() > 0)
        res.push_back(p.back());
    return res;
}

vector<int> openEdge2(int u, int v) {
    if(u == v)
        return {};
   if(minlvl(u) == evenlvl[u]) { //simply follow predecessors
        assert(predecessors[u].size() == 1); //u should be evenlevel (last minlevel edge is matched, so there is only one predecessor)
        vector<int> res = {u,predecessors[u][0]};

        int idx = 0;
        while(removed[predecessors[res.back()][idx]]) { 
            idx++; 
            assert(idx < (int)predecessors[res.back()].size());
        }

        concat(res,openEdge2(predecessors[res.back()][idx],v));
        return res;
    }
    else { //through bridge
        int u2 = myBudBridge[u].first, v2 = myBudBridge[u].second;
        int u3 = myBridge[u].from, v3 = myBridge[u].to;
        if((color[u2]^1) == color[u] || color[v2] == color[u]) {
            swap(u2, v2);
            swap(u3,v3);
        }

        vector<int> p1,p2;
        bool openingDfsSucceed1 = openingDfs(u2,u,p1);
        assert(openingDfsSucceed1);

        int v4 = myBudBridge[v] == myBudBridge[v2] ? v : bud.directParent[v2];
        bool openingDfsSucceed2 = openingDfs(v2,v4,p2);
        assert(openingDfsSucceed2);

        p1.push_back(u);
        p1 = openPath(p1);

        auto p1Prefix = openEdge2(u3,u2);
        concat(p1Prefix, p1);
        p1 = p1Prefix;
        
        p2.push_back(v4);
        p2 = openPath(p2);
        auto p2Prefix = openEdge2(v3,v2);
        concat(p2Prefix, p2);
        p2 = p2Prefix;
        
        if(v4 != v)
            concat(p2, openEdge2(v4,v));

        reverse(p1.begin(),p1.end());
        vector<int> res = {u};
        concat(p1,p2);
        concat(res,p1);
        return res;
    }
}

vector<int> openEdge(int u, int v) {
    vector<int> res = {u};
    if(find(predecessors[u].begin(),predecessors[u].end(),v) != predecessors[u].end())
        return res;
    for(auto a:predecessors[u]) {
        int cur = bud.directParent[a];
        while(cur != -1) { //speedup
            if(cur == v) {
                concat(res,openEdge2(a,v));
                return res;
            }
            cur = bud.directParent[cur];
        }
    }
    cerr<<"sth went wrong in openEdge..."<<endl;
    exit(1);
}

bool checkIfIsGoodAlternatingPath(vector<int> x) {
    bool lastMatched = false;
    for(int i=0;i+1<x.size();i++) {
        bool found = false;
        for(auto e:graph[x[i]]) {
            if(e.to == x[i+1]) {
                if(i > 0 && e.matched == lastMatched) {
                    cerr<<"not alternating"<<endl;
                    return false;
                }
                lastMatched = e.matched;
                found = true;
                break;
            }
        }
        if(!found) {
            cerr<<"invalid path"<<endl;
            return false;
        }
    }
    return true;
}

bool checkIfIsGoodAugumentingPath(vector<int> x) {
    return checkIfIsGoodAlternatingPath(x) && x.size()%2 == 0 && !isVertexMatched(x[0]);

}

bool bfs() {
    vector<vector<int> > verticesAtLevel(n);
    vector<vector<Edge> > bridges(2*n+2);

    removed.clear();
    removed.resize(n);
    vector<int> removedPredecessorsSize(n);

    for(int u=0;u<n;u++)
        if(!isVertexMatched(u)) {
            verticesAtLevel[0].push_back(u);
            setLvl(u,0);
        }

    bool foundPath = false;  
    for(int i=0;i<n && !foundPath;i++) {
        for(auto u : verticesAtLevel[i]) {
            for(auto& e:graph[u]) {
                if(e.type == NotScanned && ((oddlvl[u] == i && e.matched) || (evenlvl[u] == i && !e.matched))) { //fix
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
                        e.type = Bridge;
                        graph[e.to][e.other].type = Bridge;
                        if(tenacity(e) < INF) {
                            bridges[tenacity(e)].push_back(e);
                        }
                    }
                }
            }
        }
        

        for(auto b : bridges[2*i+1]) {
            if(removed[b.from] || removed[b.to])
                continue;
            vector<int> support;
            pair<int,int> ddfsResult = ddfs(b,support);
            if(ddfsResult.first == ddfsResult.second) {
                pair<int,int> budBridge = {bud[b.from], bud[b.to]};
                for(auto v:support) {
                    setLvl(v,2*i+1-minlvl(v));
                    verticesAtLevel[2*i+1-minlvl(v)].push_back(v);
                    myBridge[v] = b;
                    myBudBridge[v] = budBridge;
                    bud.linkTo(v,ddfsResult.first);

                    if(evenlvl[v] > oddlvl[v]) {
                        for(auto f : graph[v]) {
                            if(f.type == Bridge && tenacity(f) < INF && !f.matched) {
                                bridges[tenacity(f)].push_back(f);
                            }
                        }
                    }
                }
            }
            else {
                if(color[ddfsResult.first] != color[bud[b.from]])
                    swap(ddfsResult.first, ddfsResult.second);

                vector<int> p,q;
                openingDfs(bud[b.from],ddfsResult.first,p);
                openingDfs(bud[b.to],ddfsResult.second,q);
                p.push_back(ddfsResult.first);
                q.push_back(ddfsResult.second);
                p = openPath(p,true);
                q = openPath(q,true);
                auto x = openEdge2(b.from, bud[b.from]);
                auto y = openEdge2(b.to, bud[b.to]);
                
                concat(x,p);
                concat(y,q);
                reverse(x.begin(),x.end());
                concat(x,y);
                deb(x);
		        if(!checkIfIsGoodAugumentingPath(x)) {
                    cerr<<"wrong augumenting path!"<<endl;
                    exit(1);
                }
                foundPath = true;
                queue<int> removingVerticesQueue;
                for(auto &v: x) {
                    removed[v] = true;
                    removingVerticesQueue.push(v);
                }

                for(int j=0;j+1<x.size();j++) {
                    for(auto &e: graph[x[j]]) {
                        if(e.to == x[j+1]) {
                            e.matched ^= 1;
                            graph[e.to][e.other].matched ^= 1;
                        }
                    }
                }
                while(!removingVerticesQueue.empty()) {
                    int v = removingVerticesQueue.front();
                    removingVerticesQueue.pop();
                    for(auto e : graph[v]) {
                        if(e.type == Prop && minlvl(e.to) > minlvl(e.from) && !removed[e.to]) {
                            removedPredecessorsSize[e.to]++;
                            if(removedPredecessorsSize[e.to] == predecessors[e.to].size()) {
                                removed[e.to] = true;
                                removingVerticesQueue.push(e.to);
                            }
                        }
                    }
                }
            }
        }
    }
    return foundPath;
}

int32_t main(){
    ios::sync_with_stdio(false);
    int m;
    cin >> n >> m;
    graph.resize(n);
    for(int i=0;i<m;i++) {
        int a,b,isMatched;
        cin >> a >> b >> isMatched;
        //isMatched = false;
        graph[a].push_back({a, b, (int)graph[b].size(), isMatched, NotScanned});
        graph[b].push_back({b, a, (int)graph[a].size()-1, isMatched, NotScanned});
    }
    int iters = 0;
    do {
        iters++;
        for(auto&a: graph) {
            for(auto&e:a)
                e.type = NotScanned;
        }
        predecessors.clear();
        predecessors.resize(n);
        ddfsPredecessorsPtr.clear();
        ddfsPredecessorsPtr.resize(n);
        evenlvl.clear();
        evenlvl.resize(n,INF);
        oddlvl.clear();
        oddlvl.resize(n,INF);

        globalColorCounter = 1;
        bud.reset(n);
        color.clear();
        color.resize(n,0);
        childsInDDFSTree.clear();
        childsInDDFSTree.resize(n);
        myBudBridge.clear();
        myBudBridge.resize(n);
        myBridge.clear();
        myBridge.resize(n,{-1,-1,-1,false,NotScanned});
    }while(bfs());

    int cnt = 0;
    for(int i=0;i<n;i++)
        if(isVertexMatched(i))
            cnt++;
    cout<<cnt/2<<endl;//<<" after "<<iters<<" iterations"<<endl;
}
