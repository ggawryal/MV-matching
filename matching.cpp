//complexity O(E sqrt(V) log*(V))
#include<bits/stdc++.h>
using namespace std;
#define st first
#define nd second
typedef pair<int,int> pii;


//disjoint set union data structure
struct DSU {
    vector<int> link;
    vector<int> directParent;
    vector<int> size;
    vector<int> groupRoot;


    void reset(int n) {
        link = vector<int>(n);
        size = vector<int>(n,1);
        iota(link.begin(), link.end(), 0);
        groupRoot = link;
        directParent = vector<int>(n,-1);
    }
    
    int find(int a) {
        return link[a] = (a == link[a] ? a : find(link[a]));
    }

    int operator[](const int& a) {
        return groupRoot[find(a)];
    }

    void linkTo(int a, int b) {
        assert(directParent[a] == -1);
        assert(directParent[b] == -1);
        directParent[a] = b;
        a = find(a);
        b = find(b);
        int gr = groupRoot[b];
        assert(a != b);
        
        if(size[a] > size[b])
            swap(a,b);
        link[b] = a;
        size[a] += size[b];
        groupRoot[a] = gr;
    }

};

enum EdgeType {NotScanned, Prop, Bridge};
struct Edge {
    int to;
    int other;
    EdgeType type;
    Edge(int _to, int _other, EdgeType _type = NotScanned) : to(_to), other(_other), type(_type) {}
};

const int INF = 1e9;

int n; //IN: nuber of vertices
vector<vector<Edge> > graph; //IN: graph as neighbours list
vector<int> mate; //OUT: vertex which is matched with given, or -1 is unmatched

vector<vector<int> > predecessors;
vector<int> ddfsPredecessorsPtr;
vector<int> removed;
vector<int> evenlvl, oddlvl;
DSU bud;

int globalColorCounter; //resets to 1 after each iteration
//colors for bridges are numbered (2,3), (4,5), (6,7) ...
//to check if vertices belong to same petal check if color1/2 == color2/2
//color^1 is the other color for single ddfs run

vector<int> color;
vector<vector<pair<int,int> > > childsInDDFSTree; //{x, bud[x] at the moment when ddfs started}; may also contain other color vertices which previously were its childs 
vector<pair<pii,pii> > myBridge; // bridge, bud[bridge]


int minlvl(int u) { return min(evenlvl[u], oddlvl[u]); }

int tenacity(pii edge) {
    if(mate[edge.st] == edge.nd)
        return oddlvl[edge.st] + oddlvl[edge.nd] + 1;
    return evenlvl[edge.st] + evenlvl[edge.nd] + 1;
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
pair<int,int > ddfs(pii e, vector<int>& out_support) {
    vector<int> Sr = {bud[e.st]}, Sg = {bud[e.nd]};
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

queue<int> removedVerticesQueue;

void removeAndPushToQueue(int u) {removed[u] = 1; removedVerticesQueue.push(u);}

void flip(int u, int v) {
    if(removed[u] || removed[v] || mate[u] == v) return;//flipping only unmatched edges
    removeAndPushToQueue(u);
    removeAndPushToQueue(v);
    mate[u] = v;
    mate[v] = u;
}

void augumentPath(int a, int b, bool initial=false);

bool openingDfs(int cur, int bcur, int b) {
    if(bcur == b) {
        augumentPath(cur,bcur);
        return true;
    }
    for(auto a: childsInDDFSTree[bcur]) { 
        if((a.nd == b || color[a.nd] == color[bcur]) && openingDfs(a.st,a.nd,b)) {
            augumentPath(cur, bcur);
            flip(bcur,a.st);
            return true;
        }
    }
    return false;
}

void augumentPath(int u, int v, bool initial) {
    if(u == v) return;
    if(!initial && minlvl(u) == evenlvl[u]) { //simply follow predecessors
        assert(predecessors[u].size() == 1); //u should be evenlevel (last minlevel edge is matched, so there is only one predecessor)
        int x = predecessors[u][0]; //no need to flip edge since we know it's matched

        int idx = 0;
        while(bud[predecessors[x][idx]] != bud[x]) {
            idx++; 
            assert(idx < (int)predecessors[x].size());
        }
        u = predecessors[x][idx];
        assert(!removed[u]);
        flip(x,u);
        augumentPath(u,v);
    }
    else { //through bridge
        auto u3 = myBridge[u].st.st, v3 = myBridge[u].st.nd, u2 = myBridge[u].nd.st, v2 = myBridge[u].nd.nd;
        if((color[u2]^1) == color[u] || color[v2] == color[u]) {
            swap(u2, v2);
            swap(u3,v3);
        }

        flip(u3,v3);
        bool openingDfsSucceed1 = openingDfs(u3,u2,u);
        assert(openingDfsSucceed1);

        int v4 = bud.directParent[u];
        bool openingDfsSucceed2 = openingDfs(v3,v2,v4);
        assert(openingDfsSucceed2);
        augumentPath(v4,v);
    }
}

bool bfs() {
    vector<vector<int> > verticesAtLevel(n);
    vector<vector<pii> > bridges(2*n+2);
    vector<int> removedPredecessorsSize(n);

    auto setLvl = [&](int u, int lev) {
        if(lev&1) oddlvl[u] = lev; else evenlvl[u] = lev;
        verticesAtLevel[lev].push_back(u);
    };

    for(int u=0;u<n;u++)
        if(mate[u] == -1)
            setLvl(u,0);

    bool foundPath = false;  
    for(int i=0;i<n && !foundPath;i++) {
        for(auto u : verticesAtLevel[i]) {
            for(auto& e:graph[u]) {
                if(e.type == NotScanned && (oddlvl[u] == i) == (mate[u] == e.to)) {
                    if(minlvl(e.to) >= i+1) {
                        e.type = Prop;
                        graph[e.to][e.other].type = Prop;

                        if(minlvl(e.to) > i+1)
                            setLvl(e.to,i+1);
                        predecessors[e.to].push_back(u);
                    }
                    else {
                        e.type = Bridge;
                        graph[e.to][e.other].type = Bridge;
                        if(tenacity({u,e.to}) < INF) {
                            bridges[tenacity({u,e.to})].push_back({u,e.to});
                        }
                    }
                }
            }
        }
        
        for(auto b : bridges[2*i+1]) {
            if(removed[bud[b.st]] || removed[bud[b.nd]])
                continue;
            vector<int> support;
            auto ddfsResult = ddfs(b,support);
            pair<pii,pii> curBridge = {b,{bud[b.st], bud[b.nd]}};
            /*even when we found two disjoint paths, we create fake petal, with bud in the end of second path
            the support of this bridge will be these two pathes and some other vertices, which have bases on this paths, so we will remove them and this will not affect corectness
            using this trick, we can simply call augumentPath on these two ends - the first end is just above fake bud, so it will augument exactly the path we need
            the only problem is that some vertices in this support will be uncorrectly classified as inner/outer, so we need to pass initial=true flag to fix this case*/
            for(auto v:support) {
                if(v == ddfsResult.second) continue; //skip bud
                myBridge[v] = curBridge;
                bud.linkTo(v,ddfsResult.second);

                //this part of code is only needed when bottleneck found, but it doesn't mess up anything when called on two paths 
                setLvl(v,2*i+1-minlvl(v));
                for(auto f : graph[v])
                    if(evenlvl[v] > oddlvl[v] && f.type == Bridge && tenacity({v,f.to}) < INF && mate[v] != f.to)
                        bridges[tenacity({v,f.to})].push_back({v,f.to});
            }

            if(ddfsResult.first != ddfsResult.second) {
                augumentPath(ddfsResult.first,ddfsResult.second,true);
                foundPath = true;
                while(!removedVerticesQueue.empty()) {
                    int v = removedVerticesQueue.front();
                    removedVerticesQueue.pop();
                    for(auto e : graph[v])
                        if(e.type == Prop && minlvl(e.to) > minlvl(v) && !removed[e.to] && ++removedPredecessorsSize[e.to] == predecessors[e.to].size())
                            removeAndPushToQueue(e.to);
                }
            }
        }
    }
    return foundPath;
}

//just for testing purposes
void checkGraph() {
    for(int i=0;i<n;i++)
        assert(mate[i] == -1 || mate[mate[i]] == i);
}


void mvMatching() {
    mate = vector<int>(n,-1);
    do {
        for(auto&a: graph)
            for(auto&e:a)
                e.type = NotScanned;
        
        predecessors = vector<vector<int> > (n);
        ddfsPredecessorsPtr = color = removed = vector<int>(n);
        evenlvl = oddlvl = vector<int>(n,INF);
        childsInDDFSTree = vector<vector<pii> > (n);
        globalColorCounter = 1;
        bud.reset(n);
        myBridge = vector<pair<pii,pii> >(n);        
    }while(bfs());
    checkGraph();
}

int32_t main(){
    ios::sync_with_stdio(false);
    int m;
    cin >> n >> m;
    graph.resize(n);
    for(int i=0;i<m;i++) {
        int a,b;
        cin >> a >> b;
        graph[a].push_back(Edge(b, (int)graph[b].size()));
        graph[b].push_back(Edge(a, (int)graph[a].size()-1));
    }
    mvMatching();
    int cnt =  (n-count(mate.begin(),mate.end(),-1));
    cout<<cnt/2<<endl;
    return 0;
}
