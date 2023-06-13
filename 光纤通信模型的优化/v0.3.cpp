#include <iostream>
#include <cassert>
#include <bitset>
#include <vector>
#include <map>
#include <queue>
#include <random>
#include <ctime>
#include <algorithm>
#include <cstring>
using namespace std;

namespace {
	//global set
	const int seed=time(NULL);
	mt19937 rng(seed);
}
namespace {
	//defines & datas
	typedef pair<int,int> PII;
	const int N=5010,M=25010,inf=0x3f3f3f3f;
	const int MAXT=10010,MAXP=80,MAXD=1000;
	int n,m,T,P,D;
	int tasks[MAXT],taskt[MAXT];
	
	//edges
	struct edge {
		int from,to,d,id;
	}es[M];
	vector<edge> edges[N];
	map<PII,int> mindis;
	map<PII,vector<int> > eds;
	
	void adde(int eid,int u,int v,int d) {
		es[eid]={u,v,d,eid};
		edges[u].push_back({u,v,d,eid});
		edges[v].push_back({v,u,d,eid});
		eds[{u,v}].push_back(eid);
		eds[{v,u}].push_back(eid);
	}
	void getinput() {
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
namespace {
	//shortest dist: dijkstra
	int dist[N][N];
	struct cmp {
		static int curi;
		bool operator () (PII &p1,PII &p2) {
			//dist1+1 > dist2+1
			return dist[curi][p1.first]>dist[curi][p2.first];
		}
	};
	int cmp::curi;
	
	void getdist() {
		for(int i=0; i<n; ++i)
			for(int j=i+1; j<n; ++j)
				dist[i][j]=dist[j][i]=inf;
		for(int i=0; i<m; ++i) {
			int &u=es[i].from,&v=es[i].to;
			dist[u][v]=dist[v][u]=1;
		}
		//
		for(int &i=cmp::curi=0; i<n; ++i) {
			bitset<N> dvis;
			dvis.set(i);
			priority_queue<PII,vector<PII>,cmp> pq;
			for(edge &e:edges[i])
				pq.push({e.from,e.to});
			//
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
		exit(100);
		#endif
	}
}
namespace {
	//path record (dot pairs)
	vector<PII> taskpath[MAXT];
	
	void getpath(int tid) {
		int s=tasks[tid],t=taskt[tid];
		int mind=dist[s][t],cur=s;
		while(cur!=t) {
			mind--;
			vector<int> candidate;
			for(edge &e:edges[cur])
			if(dist[e.to][t]==mind)
				candidate.push_back(e.id);
			int eid=candidate[rng()%candidate.size()];
			taskpath[tid].push_back({es[eid].from,es[eid].to});
			cur^=es[eid].from^es[eid].to;
		}
	}
}




namespace {
	int ex,expand[N];
	bitset<MAXP> evis[M];
	int way[MAXT];
	vector<int> anspath[MAXT];
}

namespace{
	int visT[MAXT];
	bitset<MAXT> eT[M];
	int visop[N];
	int pre[N],pretid[N];
	void getbfs(int tid){
		
		for(int i=0;i<P;i++){//对每个通道查询，找到第一个能跑的通道；
			//cout<<tid<<"::"<<i<<endl;
			if(visT[tid]) break;
			for(int j=0;j<N;j++){
				visop[j]=pre[j]=pretid[j]=0;
			}
			int s=tasks[tid],t=taskt[tid];
			int cur=s;
			queue<int> qq;
			qq.push(s);
			visop[cur]=1;
			while(!qq.empty()){
				if(visT[tid]) break;
				auto uu=qq.front();qq.pop();
				for(edge &e:edges[uu]){
					//cout<<uu<<"??"<<e.from<<":::"<<e.to<<endl;
					if(visop[e.to]) continue;//不走重
					if(evis[e.id].test(i)){//这个通道用过;
						continue;
					}
					pre[e.to]=e.from;
					//cout<<e.from<<"???"<<e.to<<"??"<<visop[1]<<"??"<<t<<endl;
					pretid[e.to]=e.id;
					if(e.to==t){//找到路径；
						visT[tid]=1;
						vector<int> ac;
						int check=e.to;
						//cout<<e.to<<":::"<<endl;
						//int kkkk=3;
						while(check!=s){
							//cout<<check<<"::::"<<endl;
							ac.push_back(pretid[check]);
							evis[pretid[check]].set(i);
							check=pre[check];
						}
						way[tid]=i;
						//ac.push_back(s);
						int len=ac.size();
						for(int j=len-1;j>=0;j--){
							anspath[tid].push_back(ac[j]);
						}
						break;
					}
					//
					visop[e.to]=1;
					qq.push({e.to});
				}
			}
		}
	}
}

int main() {
	//inits
	getinput();
	getdist();
	for(int i=0; i<T; ++i)
		getpath(i);
	//
	//
	for(int i=0;i<T;i++){
		getbfs(i);
		//cout<<visT[i]<<"??????0"<<endl;
	}

	for(int i=0; i<T; ++i) {
		
		if(visT[i]) continue;
		bitset<MAXP> vis,tmp;
		for(PII &pr:taskpath[i]) {
			vector<int> &eids=eds[pr];
			tmp.set();
			for(int eid:eids)
				tmp&=evis[eid];
			//add edge
			if((vis|tmp).count()!=(unsigned)P)vis|=tmp;
			else adde(m+ex++,pr.first,pr.second,mindis[pr]);
		}
		//get mex
		int mex=MAXP;
		for(int j=0; j<P; ++j)
		if(vis[j]==0) {
			mex=j;
			break;
		}
		if(0 && mex==MAXP) {
			for(PII &pr:taskpath[i])
				adde(m+ex++,pr.first,pr.second,mindis[pr]);
			mex=0;
		}
		way[i]=mex;
		//get anspath & set evis
		for(PII &pr:taskpath[i]) {
			vector<int> &eids=eds[pr];
			for(int eid:eids)
			if(!evis[eid].test(mex)) {
				anspath[i].push_back(eid);
				evis[eid].set(mex);
				break;
			}
		}
	}
	//output
	printf("%d\n",ex);
	for(int i=m; i<m+ex; ++i)
		printf("%d %d\n",es[i].from,es[i].to);
	for(int i=0; i<T; ++i) {
		int d=0,expcnt=0,t=taskt[i];
        int s=taskt[i];
        int pos;
		for(int eid:anspath[i]) {
			d+=es[eid].d;
            if(es[eid].from==s){
                pos=es[eid].from;
                s=es[eid].to;
            }
            else{
                pos=es[eid].to;
                s=es[eid].from;
            }
			if(d>D) {
				//int pos=dist[t][es[eid].from]>dist[t][es[eid].to]?es[eid].from:es[eid].to;
				expand[expcnt++]=pos;
				d=es[eid].d;     //能否优化
			}
		}
		//p m n
		printf("%d %d %d",way[i],(int)anspath[i].size(),expcnt);
		for(int eid:anspath[i])printf(" %d",eid);
		for(int j=0; j<expcnt; ++j)printf(" %d",expand[j]);
		printf("\n");
	}
}
