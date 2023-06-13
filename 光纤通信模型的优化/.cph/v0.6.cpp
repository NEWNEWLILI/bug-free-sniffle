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

//玄学排序
namespace{

    struct qqq{
        int s,t;
        int di,id;
    }taskk[MAXT];
    bool cmp2(qqq a,qqq b){
        return a.di<b.di;
    }
}

namespace {
	int ex,expand[N];
	bitset<MAXP> evis[M];
	int way[MAXT];
	vector<int> anspath[MAXT];
}

namespace{//先把能处理的都处理；
	int visT[MAXT];
	bitset<MAXT> eT[M];
	int visop[N];
	int pre[N],pretid[N];
    vector<int> suiji;
    int visbb[N];
	int getbfs(int tid){
        vector<int> tmpp=suiji;
        vector<int> key;
        for(int i=0;i<P;i++) visbb[i]=0;
        for(int i=0;i<P;i++){
            int uu=rng()%P;
            for(int j=uu;j<P;j++){
                if(visbb[j]) continue;
                else{
                    visbb[j]=1;
                    key.push_back(tmpp[j]);
                }
            }
            if(key.size()>i) continue;
            for(int j=0;j<uu;j++){
                if(visbb[j]) continue;
                else{
                    visbb[j]=1;
                    key.push_back(tmpp[j]);
                }
            }
        }
        // for(int i=0;i<P;i++) {
        //     cout<<key[i]<<"::"<<tid<<endl;
        // }
		for(int i=0;i<P;i++){//对每个通道查询，找到第一个能跑的通道；
			//cout<<tid<<"::"<<i<<endl;
			if(visT[taskk[tid].id]) break;
			for(int j=0;j<N;j++){
				visop[j]=pre[j]=pretid[j]=0;
			}
			int s=tasks[taskk[tid].id],t=taskt[taskk[tid].id];
			int cur=s;
			queue<int> qq;
			qq.push(s);
			visop[cur]=1;
			while(!qq.empty()){
				if(visT[taskk[tid].id]) break;
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
						visT[taskk[tid].id]=1;
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
						way[taskk[tid].id]=i;
						//ac.push_back(s);
						int len=ac.size();
						for(int j=len-1;j>=0;j--){
							anspath[taskk[tid].id].push_back(ac[j]);
						}
						break;
					}
					//
					visop[e.to]=1;
					qq.push({e.to});
				}
			}
		}
        return visT[taskk[tid].id];
	}
}

namespace{//处理需要加边的；
    void getlast(int tid){
        for(int i=0;i<P;i++){
            int s=tasks[tid],t=taskt[tid];
            queue<pair<int,int> > qq;

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
    for(int i=0;i<P;i++){
        suiji.push_back(i);
    }
    for(int i=0;i<T;i++){
        taskk[i].di=dist[tasks[i]][taskt[i]];
        taskk[i].s=tasks[i];
        taskk[i].t=taskt[i];
        taskk[i].id=i;
    }
    sort(taskk,taskk+T,cmp2);
    for(int i=T-1; i>=0; i--) {
		//if(visT[i]) continue;
		bitset<MAXP> vis,tmp;
        int yy=0;
		for(PII &pr:taskpath[taskk[i].id]) {
			vector<int> &eids=eds[pr];
			tmp.set();
			for(int eid:eids)
				tmp&=evis[eid];
			//add edge
			if((vis|tmp).count()!=(unsigned)P)vis|=tmp;
			//else adde(m+ex++,pr.first,pr.second,mindis[pr]);
            else {
                yy=1;
            }
		}
        if(yy==1) continue;
        else{
            visT[taskk[i].id]=1;
        }
		//get mex
		int mex=MAXP;
		for(int j=0; j<P; ++j)
		if(vis[j]==0) {
			mex=j;
			break;
		}
		if(0 && mex==MAXP) {
			for(PII &pr:taskpath[taskk[i].id])
				adde(m+ex++,pr.first,pr.second,mindis[pr]);
			mex=0;
		}
		way[taskk[i].id]=mex;
		//get anspath & set evis
		for(PII &pr:taskpath[taskk[i].id]) {
			vector<int> &eids=eds[pr];
			for(int eid:eids)
			if(!evis[eid].test(mex)) {
				anspath[taskk[i].id].push_back(eid);
				evis[eid].set(mex);
				break;
			}
		}
	}
	for(int i=T-1;i>=0;i--){
        if(visT[taskk[i].id]) continue;

		getbfs(i);
	}
    
	for(int i=T-1; i>=0; i--) {
		if(visT[taskk[i].id]) continue;

        if(getbfs(i)) continue;
		bitset<MAXP> vis,tmp;
		for(PII &pr:taskpath[taskk[i].id]){
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
			for(PII &pr:taskpath[taskk[i].id])
				adde(m+ex++,pr.first,pr.second,mindis[pr]);
			mex=0;
		}
		way[taskk[i].id]=mex;
		//get anspath & set evis
		for(PII &pr:taskpath[taskk[i].id]) {
			vector<int> &eids=eds[pr];
			for(int eid:eids)
			if(!evis[eid].test(mex)) {
				anspath[taskk[i].id].push_back(eid);
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
        int s=tasks[i];
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
