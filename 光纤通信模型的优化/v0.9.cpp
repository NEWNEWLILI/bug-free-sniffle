#include <iostream>
#include <bitset>
#include <map>
#include <queue>
#include <random>
#include <ctime>
#include <algorithm>
using namespace std;

namespace glob {
	//global set
	typedef pair<int,int> PII;
	typedef double fl;
	const int seed=time(NULL);
	mt19937 rng(seed);
}
using namespace glob;

namespace info {
	//defines & datas
	const int N=5010,M=25010,inf=0x3f3f3f3f;
	const int MAXT=10010,MAXP=80,MAXD=1000;
	map<PII,int> mp,used;
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
			if(u>v) swap(u,v);
			mp[{u,v}]+=P;
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
	int ex,expand[N];
	bitset<MAXP> evis[M];
	int sq[MAXT],way[MAXT];
	vector<int> anspath[MAXT];
	
	bool id_cmp(int i,int j) {
		return dist[tasks[i]][taskt[i]]>dist[tasks[j]][taskt[j]];
	}
}
using namespace core;

namespace prep {
	//shortest dot_pairs_path record
	//at most candi_cnt candidate shortest pathes
	const int candi_cnt=100;
	vector<PII> prepath[MAXT][candi_cnt];
	
	//length <= min_dist+tolerance treated as shortest path
	const int tolerance=0;
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
			vis.set(s);
			prep_dfs(1,s);
			vis.reset(s);
		}
	}
	int getchoose(int i) {
		int p,mincnt=inf;
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
	void getanspath(int tid,bitset<MAXP> &vis,int path_choose) {
		//get way
		int &mex=way[tid]=-1;
		for(int i=0; i<P; ++i)
		if(!vis.test(i)) {
			mex=i;
			break;
		}
		if(mex==-1)return;
		//get anspath & update evis
		for(PII &pr:prepath[tid][path_choose]) {
			vector<int> &eids=eds[pr];
			for(int eid:eids)
			if(!evis[eid].test(mex)) {
				anspath[tid].push_back(eid);
				evis[eid].set(mex);
				break;
			}
		}
	}
	
	bitset<N> vis;
	int preeid[N];
	bool bfs(int tid) {
		int s=tasks[tid],t=taskt[tid];
		//find first available way
		for(int i=0; i<P; i++) {
			vis.reset();
			vis.set(s);
			queue<PII> q;
			q.push({s,0});
			while(!q.empty()) {
				auto ik=q.front();
				int cur=q.front().first;q.pop();
				if(cur==t) {
					// if(ik.second>dist[s][t]+70){
					// 	break;
					// }
					way[tid]=i;
					//get anspath & update evis
					while(cur!=s) {
						int &eid=preeid[cur];
						evis[eid].set(i);
						anspath[tid].push_back(eid);
						cur^=es[eid].from^es[eid].to;
					}
					reverse(anspath[tid].begin(),anspath[tid].end());
					return true;
				}
				for(edge &e:edges[cur])
				if(!vis.test(e.to) && !evis[e.id].test(i)) {
					vis.set(e.to);
					q.push({e.to,ik.second+1});
					preeid[e.to]=e.id;
				}
			}
		}
		return false;
	}
}
using path::getanspath;
using path::bfs;

int main() {
	//inits
	getinput();
	getdist();
	for(int i=0; i<T; ++i)
		getprepath(i);
	#define showprepath false
	#if showprepath
	for(int i=0; i<T; ++i) {
		cout<<i<<": "<<endl;
		for(int j=0; j<prep::candi_cnt; ++j) {
			vector<PII> &v=prepath[i][j];
			for(PII &pr:v)
				cout<<pr.first<<' '<<pr.second<<"   ";
			cout<<endl;
		}
	}
	exit(2);
	#endif
	//long -> short
	for(int i=0; i<T; ++i)sq[i]=i;
	sort(sq,sq+T,id_cmp);
	//try prepath
	for(int idx=0,i=sq[0]; idx<T; ++idx,i=sq[idx]){
		int path_choose=0;
		for(PII &pr:prepath[i][path_choose]){
			if(pr.first>pr.second){
				swap(pr.first,pr.second);
			}
			used[pr]++;
		}
	}
	for(int idx=0,i=sq[0]; idx<0.7*T; ++idx,i=sq[idx]){
		int path_choose=0;
		int pre_sum=0;
		for(PII &pr:prepath[i][path_choose]){
			if(pr.first>pr.second){
				swap(pr.first,pr.second);
			}
			used[pr]--;
			pre_sum=pre_sum+mp[pr]-used[pr];
		}
		int pre_idx=0;
		for(int j=1;j<prep::candi_cnt;j++){
			int sum=0;
			for(PII &pr:prepath[i][j]){
				if(pr.first>pr.second){
					swap(pr.first,pr.second);
				}
				sum=sum+mp[pr]-used[pr];
			}
			if(sum>pre_sum){
				pre_idx=j;pre_sum=sum;
			}
		}
		//cout<<pre_idx<<"::"<<endl;
		//swap(prepath[i][0],prepath[i][pre_idx]);
		for(PII &pr:prepath[i][path_choose]){
			if(pr.first>pr.second){
				swap(pr.first,pr.second);
			}
			used[pr]++;
		}
	}
	for(int idx=0,i=sq[0]; idx<T; ++idx,i=sq[idx]) {
		bitset<MAXP> vis,tmp;
		int path_choose=0;
		for(PII &pr:prepath[i][path_choose]) {
			tmp.set();
			vector<int> &eids=eds[pr];
			for(int eid:eids)
				tmp&=evis[eid];
			vis|=tmp;
			if(vis.count()==(unsigned)P)break;
		}
		getanspath(i,vis,path_choose);
	}
	//try bfs
	for(int idx=0,i=sq[0]; idx<0.888*T; ++idx,i=sq[idx])
		if(!anspath[i].size() && !bfs(i));
	//bfs else brute force the prepath
	for(int idx=0,i=sq[0]; idx<T; ++idx,i=sq[idx])
	if(!anspath[i].size() && !bfs(i)){
		int path_choose=0;
		// for(PII &pr:prepath[i][path_choose]) {
		// 	tmp.set();
		// 	vector<int> &eids=eds[pr];
		// 	for(int eid:eids)
		// 		tmp&=evis[eid];
		// 	//add edge
		// 	if((vis|tmp).count()!=(unsigned)P)vis|=tmp;
		// 	else adde(m+ex++,pr.first,pr.second,mindis[pr]);
		// }
		int uu=0;
		
		for(int j=0;j<prep::candi_cnt;j++){
			bitset<MAXP> vis,tmp;
			int qq=0;
			for(PII &pr:prepath[i][j]) {
				tmp.set();
				vector<int> &eids=eds[pr];
				for(int eid:eids)
					tmp&=evis[eid];
				//add edge
				if((vis|tmp).count()!=(unsigned)P)vis|=tmp;
				else qq++;
			}
			if(j==0){
				uu=qq;
			}
			else{
				if(uu>qq){
					uu=qq;
					path_choose=j;
				}
			}
		}
		bitset<MAXP> viss,tmpp;
		for(PII &pr:prepath[i][path_choose]) {
			tmpp.set();
			vector<int> &eids=eds[pr];
			for(int eid:eids)
				tmpp&=evis[eid];
			//add edge
			if((viss|tmpp).count()!=(unsigned)P)viss|=tmpp;
			else adde(m+ex++,pr.first,pr.second,mindis[pr]);
		}
		getanspath(i,viss,path_choose);
	}
	//fan hui qu jian cha

	

	//output
	printf("%d\n",ex);
	for(int i=m; i<m+ex; ++i)
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
	}
}
