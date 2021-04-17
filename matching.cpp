#include<bits/stdc++.h>
using namespace std;
#define st first
#define nd second
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
vector<vector<pair<int,int> > > childsInDDFSTree; //{x, bud[x] at the moment when ddfs started}; may also contain other color vertices which previously were its childs 

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
    for(; ddfsPredecessorsPtr[u] < predecessors[u].size(); ddfsPredecessorsPtr[u]++) {
        int a = predecessors[u][ddfsPredecessorsPtr[u]];
        int v = bud[a];
        assert(removed[a] == removed[v]);
        if(removed[a])
            continue;
        if(color[v] == 0) {
            stack1.push_back(v);
            support.push_back(v);
            childsInDDFSTree[u].push_back({a,v});
            color[v] = color1;
            return -1;
        }
        else if(v == stack2.back())
            childsInDDFSTree[u].push_back({a,v});
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
    if(Sr[0] == Sg[0])
        return {Sr[0],Sg[0]};

    out_support = {Sr[0], Sg[0]};
    int newRed = color[Sr[0]] = ++globalColorCounter, newGreen = color[Sg[0]] = ++globalColorCounter;
    assert(newRed == (newGreen^1));

    for(;;) {
        //if found two disjoint paths
        if(minlvl(Sr.back()) == 0 && minlvl(Sg.back()) == 0)
            return {Sr.back(),Sg.back()};
    
        int b;
        if(minlvl(Sr.back()) >= minlvl(Sg.back()))
            b = ddfsMove(Sr,newRed,Sg, newGreen, out_support);
        else
            b = ddfsMove(Sg,newGreen,Sr, newRed, out_support);
        if(b != -1)
            return {b,b};
    }
}

bool isVertexMatched(int u) {
    for(auto e:graph[u])
        if(e.matched)
            return true;
    return false;
}

bool openingDfs(int cur, int bcur, int b,vector<pii>& outPath) {
    outPath.push_back({cur,bcur});
    
    if(bcur == b)
        return true;
    for(auto a: childsInDDFSTree[bcur]) { 
        if((a.nd == b || color[a.nd] == color[bcur]) && /*!removed[a.nd] &&*/ openingDfs(a.st,a.nd,b,outPath))
            return true;
    }
    outPath.pop_back();
    return false;
}

void concat(vector<int>& a, const vector<int>& b) {
    for(auto x : b)
        a.push_back(x);
}


vector<int> openPath(vector<pii> p, bool initial = false) {
    vector<int> res;
    for(auto [u,v] : p) {
        if(u == v)
            res.push_back(u);
        else if(!initial && minlvl(u) == evenlvl[u]) { //simply follow predecessors
            assert(predecessors[u].size() == 1); //u should be evenlevel (last minlevel edge is matched, so there is only one predecessor)
            concat(res,{u,predecessors[u][0]});

            int idx = 0;
            while(bud[predecessors[res.back()][idx]] != bud[res.back()]) {
                idx++; 
                assert(idx < (int)predecessors[res.back()].size());
            }
            assert(!removed[predecessors[res.back()][idx]]);
            concat(res,openPath({{predecessors[res.back()][idx],v}}));
        }
        else { //through bridge
            int u2 = myBudBridge[u].first, v2 = myBudBridge[u].second;
            int u3 = myBridge[u].from, v3 = myBridge[u].to;
            if((color[u2]^1) == color[u] || color[v2] == color[u]) {
                swap(u2, v2);
                swap(u3,v3);
            }

            vector<pii> p1,p2;
            bool openingDfsSucceed1 = openingDfs(u3,u2,u,p1);
            assert(openingDfsSucceed1);
            
            int v4 = myBudBridge[v] == myBudBridge[v2] ? v : bud.directParent[v2];
            bool openingDfsSucceed2 = openingDfs(v3,v2,v4,p2);
            assert(openingDfsSucceed2);

            auto op1 = openPath(p1);
            auto op2 = openPath(p2);
            if(v4 != v) {
                op2.pop_back();
                concat(op2, openPath({{v4,v}}));
            }
            reverse(op1.begin(),op1.end());
            concat(op1,op2);
            concat(res,op1);
        }
    }
    return res;
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
                if(e.type == NotScanned && (oddlvl[u] == i) == e.matched) {
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
            pair<int,int> budBridge = {bud[b.from], bud[b.to]};

            for(auto v:support) {
                if(v == ddfsResult.second) continue; //skip bud
                myBridge[v] = b;
                myBudBridge[v] = budBridge;
                bud.linkTo(v,ddfsResult.second);

                //this part of code is only needed when bottleneck found, but it don't mess up anything when called on two paths
                verticesAtLevel[2*i+1-minlvl(v)].push_back(v);
                setLvl(v,2*i+1-minlvl(v));

                for(auto f : graph[v])
                    if(evenlvl[v] > oddlvl[v] && f.type == Bridge && tenacity(f) < INF && !f.matched)
                        bridges[tenacity(f)].push_back(f);
            }

            if(ddfsResult.first != ddfsResult.second) {
                auto p = openPath({{ddfsResult.first,ddfsResult.second}},true);
		        if(!checkIfIsGoodAugumentingPath(p)) {
                    cerr<<"wrong augumenting path!"<<endl;
                    exit(1);
                }
                foundPath = true;
                queue<int> removingVerticesQueue;
                for(auto &v: p) {
                    removed[v] = true;
                    removingVerticesQueue.push(v);
                }

                for(int j=0;j+1<p.size();j++) {
                    for(auto &e: graph[p[j]]) {
                        if(e.to == p[j+1]) {
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
