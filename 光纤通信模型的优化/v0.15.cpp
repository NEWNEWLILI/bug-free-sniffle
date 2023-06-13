#pragma GCC optimize(3)
#include <iostream>
#include <bitset>
#include <map>
#include <queue>
#include <random>
#include <ctime>
#include <algorithm>
#include <cassert>
using namespace std;

namespace glob {
	//global set
	typedef pair<int,int> PII;
	typedef long long ll;
	typedef double fl;
	const int seed=time(NULL);
	mt19937 rng(seed);
}
using namespace glob;

namespace info {
	//defines & datas
	const int N=5010,M=25010,inf=0x3f3f3f3f;
	const int MAXT=10010,MAXP=80,MAXD=1000;
	int n,m,T,P,D;
	int tasks[MAXT],taskt[MAXT];
	
	//edges
	struct edge {
		int from,to,d,id;
	}es[M];							//undirect edges
	vector<edge> edges[N];			//directed edges
	map<PII,int> mindis;			//dot pair -> shortest_edge_dist
	map<PII,vector<int> > eds;		//dot pair -> edges_between_them_id
	
	void adde(int eid,int u,int v,int d) {
		es[eid]={u,v,d,eid};
		edges[u].push_back({u,v,d,eid});
		edges[v].push_back({v,u,d,eid});
		eds[{u,v}].push_back(eid);
		eds[{v,u}].push_back(eid);
	}
	void getinput() {
		//get n m T P D
		//and all edges, tasks
		scanf("%d%d%d%d%d",&n,&m,&T,&P,&D);
		for(int i=0,u,v,d; i<m; ++i) {
			scanf("%d%d%d",&u,&v,&d);
			adde(i,u,v,d);
			if(!mindis.count({u,v}))mindis[{u,v}]=inf;
			mindis[{u,v}]=mindis[{v,u}]=min(mindis[{u,v}],d);
		}
		for(int i=0; i<T; ++i)
			scanf("%d%d",&tasks[i],&taskt[i]);
	}
}
using namespace info;

namespace mind {
	//shortest dist: dijkstra
	int dist[N][N];
	struct dj_cmp {
		static int curi;
		bool operator () (PII &p1,PII &p2) {
			//dist1+1 > dist2+1
			return dist[curi][p1.first]>dist[curi][p2.first];
		}
	};
	int dj_cmp::curi;
	
	void getdist() {
		for(int i=0; i<n; ++i)
			for(int j=i+1; j<n; ++j)
				dist[i][j]=dist[j][i]=inf;
		for(int i=0; i<m; ++i) {
			int &u=es[i].from,&v=es[i].to;
			dist[u][v]=dist[v][u]=1;
		}
		//get minimum distance for all dot as start_pos
		for(int &i=dj_cmp::curi=0; i<n; ++i) {
			bitset<N> dvis;
			dvis.set(i);
			priority_queue<PII,vector<PII>,dj_cmp> pq;
			for(edge &e:edges[i])
				pq.push({e.from,e.to});
			//choose shortest unvisit_dot each time
			while(!pq.empty()) {
				PII pr=pq.top();pq.pop();
				int &u=pr.first,&v=pr.second;
				if(!dvis.test(v)) {
					dvis.set(v);
					dist[i][v]=dist[i][u]+1;//update dist
					for(edge &e:edges[v])
					if(!dvis.test(e.to))
						pq.push({v,e.to});
				}
			}
		}
		#define showdist false
		#if showdist
		for(int i=0; i<n; ++i) {
			cout<<i<<": ";
			for(int j=0; j<n; ++j)
				cout<<j<<"("<<dist[i][j]<<") ";
			cout<<endl;
		}
		exit(1);
		#endif
	}
}
using namespace mind;

namespace core {
	int execnt;					//current extra edge count
	int expand[N];				//i_th signal_expand_pos of current task
	bitset<MAXP> evis[M];		//way_use of i_th edge
	vector<int> sq(MAXT);		//task process order
	int way[MAXT];				//result_way record (0~P-1)
	vector<int> anspath[MAXT];	//result_path record (eid)
	
	ll cost,totexpcnt;			//for scoring
	
	//used to rearrange the process order
	bool id_cmp(int i,int j) {
		return dist[tasks[i]][taskt[i]]>dist[tasks[j]][taskt[j]];
	}
	//used to update evis
	bool set_path(vector<int> &eidpath,int way_choose) {
		for(int &eid:eidpath)
		if(evis[eid].test(way_choose))
			return false;
		for(int &eid:eidpath)evis[eid].set(way_choose);
		return true;
	}
	void rid_path(vector<int> &eidpath,int way_choose) {
		for(int &eid:eidpath)evis[eid].reset(way_choose);
	}
}
using namespace core;

namespace prep {
	//shortest dot_pairs_path record
	//at most candi_cnt candidate shortest pathes
	const int candi_cnt=10;
	vector<PII> prepath[MAXT][candi_cnt];
	
	//length <= min_dist+tolerance treated as shortest path
	int tolerance=0;
	bitset<N> vis;
	int s,t,tid,cid,path[N];
	void suffle_choose(vector<int> &tos) {
		int len=tos.size();
		for(int i=0; i<len; ++i)
			swap(tos[i],tos[i+rng()%(len-i)]);
	}
	bool prep_dfs(int deep,int cur) {
		path[deep]=cur;
		if(cur==t) {
			//path[1,deep] : s->t
			for(int i=1,j=2; i<deep; ++i,++j) {
				vis.reset(path[j]);
				prepath[tid][cid].push_back({path[i],path[j]});
			}
			return true;
		}
		//
		vector<int> tos;
		for(edge &e:edges[cur])
		if(!vis.test(e.to) && deep+dist[e.to][t]<=dist[s][t]+tolerance)
			tos.push_back(e.to);
		//
		suffle_choose(tos);
		for(int i=0,I=tos.size(); i<I; ++i) {
			for(int j=0; j<i; ++j)
			if(tos[i]==tos[j]) {
				tos.erase(tos.begin()+i);
				i--,I--;
				break;
			}
		}
		//
		for(int to:tos) {
			vis.set(to);
			if(prep_dfs(deep+1,to))return true;
			vis.reset(to);
		}
		return false;
	}
	void getprepath(int taskid) {
		tid=taskid;
		s=tasks[tid],t=taskt[tid];
		for(cid=0; cid<candi_cnt; ++cid) {
			tolerance=cid>4;
			vis.set(s);
			prep_dfs(1,s);
			vis.reset(s);
		}
	}
	//get path_choose from candi_cnt pathes
	int getchoose(int i) {
		int p=-1,mincnt=inf;
		for(int j=0; j<candi_cnt; ++j) {
			bitset<MAXP> vis,tmp;
			int cnt=0;
			for(PII &pr:prepath[i][j]) {
				tmp.set();
				vector<int> &eids=eds[pr];
				for(int eid:eids)
					tmp&=evis[eid];
				if((vis|tmp).count()!=(unsigned)P)vis|=tmp;
				else cnt++;
			}
			if(cnt<mincnt) {
				mincnt=cnt;
				p=j;
			}
		}
		return p;
	}
}
using prep::prepath;
using prep::getprepath;
using prep::getchoose;

namespace path {
	void getanspath01(int tid,int path_choose,int way_choose) {
		way[tid]=way_choose;
		//get anspath & update evis
		for(PII &pr:prepath[tid][path_choose]) {
			vector<int> &eids=eds[pr];
			for(int eid:eids)
			if(!evis[eid].test(way_choose)) {
				anspath[tid].push_back(eid);
				evis[eid].set(way_choose);
				break;
			}
		}
	}
	void getanspath(int tid,bitset<MAXP> &vis,int path_choose) {
		//find first available way
		for(int w=0; w<P; ++w)
		if(!vis.test(w))
			return getanspath01(tid,path_choose,w);
	}
	
	bool cmp_76ab(int &a,int &b) {
		return ((a&0xffff)^0x76ab)<((b&0xffff)^0x76ab);
	}
	
	bitset<N> vis;
	int preeid[N],least_dist;
	bool bfs01(int tid,int way_choose) {
		int &s=tasks[tid],&t=taskt[tid];
		vis.reset();
		vis.set(s);
		queue<int> q;
		q.push(s);
		while(!q.empty()) {
			int cur=q.front();q.pop();
			if(cur==t) {
				int d=0;
				while(cur!=s) {
					d++;
					cur^=es[preeid[cur]].from^es[preeid[cur]].to;
				}
				//get anspath
				if(d<least_dist) {
					least_dist=d;
					way[tid]=way_choose;
					anspath[tid].clear();
					cur=t;
					while(cur!=s) {
						int &eid=preeid[cur];
						anspath[tid].push_back(eid);
						cur^=es[eid].from^es[eid].to;
					}
				}
				return true;
			}
			vector<int> tos;
			for(edge &e:edges[cur])
			if(!vis.test(e.to) && !evis[e.id].test(way_choose)) {
				vis.set(e.to);
				tos.push_back(e.to);
				preeid[e.to]=e.id;
			}
			sort(tos.begin(),tos.end(),cmp_76ab);
//			prep::suffle_choose(tos);
			for(int to:tos)q.push(to);
		}
		return false;
	}
	bool bfs(int tid) {
		//find first available way
		for(int i=0; i<P; i++)
		if(bfs01(tid,i))
			return true;
		return false;
	}
}
using path::getanspath;
using path::bfs;
using path::getanspath01;
using path::bfs01;

namespace bfs2 {
	bitset<N> vis;
	int rnd[N],preeid[N],s,t;
	struct xbfs_cmp {
		//first: s_cur_dist, second: from_eid<<16|cur_pos
		bool operator () (PII &p1,PII &p2) {
			return p1.first>p2.first || (p1.first==p2.first && !path::cmp_76ab(p1.second,p2.second));//rnd[p1.second&0xffff]>rnd[p2.second&0xffff]);
		}
	};
	//union-find disjoint sets
	struct {
		int f[N],sz[N];
		int find(int x) {
			if(x==f[x])return x;
			return f[x]=find(f[x]);
		}
		void link(int a,int b) {
			if(find(a)==find(b))return;
			if(sz[f[a]]<sz[f[b]])swap(a,b);
			sz[f[a]]+=sz[f[b]];
			f[f[b]]=f[a];
		}
	}sets[MAXP];
	
	int least_dist;
	//dijkstra
	void xbfs01(int tid,int way_choose) {
		priority_queue<PII,vector<PII>,xbfs_cmp> pq;
		pq.push({0,s});
		vis.reset();
		while(!pq.empty()) {
			PII tmp=pq.top();pq.pop();
			int cur=tmp.second&0xffff,&d=tmp.first;
			if(vis.test(cur))continue;
			vis.set(cur);
			preeid[cur]=tmp.second>>16;
			if(cur==t) {
				if(d<least_dist) {
					least_dist=d;
					way[tid]=way_choose;
					anspath[tid].clear();
					while(cur!=s) {
						int &eid=preeid[cur];
						anspath[tid].push_back(eid);
						cur^=es[eid].from^es[eid].to;
					}
				}
				return;
			}
			for(edge &e:edges[cur])
			if(!vis.test(e.to)) {
				int dis=evis[e.id].test(way_choose)?100000:1;
				pq.push({d+dis,e.id<<16|e.to});
			}
		}
	}
	
	void xbfs(int tid) {
		//init rnd
		iota(rnd,rnd+n,0);
		random_shuffle(rnd,rnd+n);
		//work
		least_dist=inf;
		s=tasks[tid],t=taskt[tid];
		for(int w=0; w<P; ++w)xbfs01(tid,w);
		//add edge
		for(int &eid:anspath[tid])
		if(evis[eid].test(way[tid])) {
			edge &e=es[eid];
			adde(eid=m+execnt++,e.from,e.to,mindis[{e.from,e.to}]);
		}
	}
}
using bfs2::xbfs;
using bfs2::sets;

void solve() {
	//init sets
	for(int w=0; w<P; ++w) {
		sets[w].sz[0]=n;
		for(int i=0; i<n; ++i)sets[w].f[i]=0;
	}
	//find current minimum cost
	for(int idx=0,i=sq[idx]; idx<T; ++idx,i=sq[idx]) {
		path::least_dist=inf;
		for(int w=0,s=tasks[i],t=taskt[i]; w<P; ++w)
		if(sets[w].find(s)==sets[w].find(t))
			assert(bfs01(i,w));
		if(anspath[i].empty())xbfs(i);
		int way_rec=way[i];
		reverse(anspath[i].begin(),anspath[i].end());
		//update evis & sets
		assert(set_path(anspath[i],way_rec));
		for(int j=0; j<n; ++j) {
			sets[way_rec].f[j]=j;
			sets[way_rec].sz[j]=1;
		}
		for(int j=0; j<m+execnt; ++j)
		if(!evis[j].test(way_rec))
			sets[way_rec].link(es[j].from,es[j].to);
	}
}


int main(int argc,char *args[]) {
	#define datatest false
	if(argc==2 || datatest) {
		char file[]="data0.txt";
		char *s=(argc==2?args[1]:file);
		freopen(s,"r",stdin);
		freopen("answer.txt","w",stdout);
	}
	//inits
	getinput();
	getdist();
	for(int i=0; i<T; ++i)
		getprepath(i);
	//long -> short
	iota(sq.begin(),sq.begin()+T,0);
	sort(sq.begin(),sq.begin()+T,id_cmp);
	//
//	time_t t0=clock();
	solve();
//	cerr<<(clock()-t0)/1000.<<'s'<<endl;
	//output
	printf("%d\n",execnt);
	for(int i=m; i<m+execnt; ++i)
		printf("%d %d\n",es[i].from,es[i].to);
	for(int i=0; i<T; ++i) {
		int d=0,expcnt=0,cur=tasks[i];
		for(int eid:anspath[i]) {
			d+=es[eid].d;
			if(d>D) {
				expand[expcnt++]=cur;
				d=es[eid].d;
			}
			cur^=es[eid].from^es[eid].to;
		}
		//p m n
		printf("%d %d %d",way[i],(int)anspath[i].size(),expcnt);
		for(int eid:anspath[i])printf(" %d",eid);
		for(int j=0; j<expcnt; ++j)printf(" %d",expand[j]);
		printf("\n");
		totexpcnt+=expcnt;
	}
	//
	if(argc==2 || datatest) {
		freopen("CON","w",stdout);
		freopen("CON","r",stdin);
		cost=execnt*1000000ll+totexpcnt*100;
		for(int i=0; i<T; ++i)cost+=anspath[i].size();
		cout<<cost<<endl;
		int taskmaxdist=0;
		for(int i=0; i<T; ++i)
			taskmaxdist=max(taskmaxdist,dist[tasks[i]][taskt[i]]);
		cout<<taskmaxdist<<endl;
		cin>>cost;
	}
}
