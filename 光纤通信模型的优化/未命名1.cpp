#include <iostream>
#include <bits/stdc++.h>
using namespace std;
#define int long long
#define N 550000
int a[20][N];
int maxx[20][N];
int f[N*10];
signed main(){
	int n;
	cin>>n;
	for(int i=1;i<=n;i++){
		int k=(1<<(n-i));
		for(int j=1;j<=k;j++){
			cin>>a[i][j];
		}
	}
	int ans; 
	cin>>ans;
	int flag=0;
	for(int i=1;i<=n;i++){
		int len=(1<<(n-i));
		for(int j=1;j<=len;j++){
			int g=j;
			for(int u=i;u>0;u--){
				//cout<<u<<"::"<<endl;
				maxx[u][g]++;
				int l=a[u-1][g*2-1],r=a[u-1][g*2];
				//cout<<l<<"::"<<r<<"::"<<a[u][g]<<endl;
				if(a[u][g]>=l&&a[u][g]>=r){
					//cout<<maxx[u-1][g*2-1]<<"::"<<endl;
					if(l>=r&&(maxx[u-1][g*2-1]<(1<<(u-1)))){
						//cout<<a[u][g]<<"??"<<u<<"::"<<g<<endl;
						a[u-1][g*2-1]=a[u][g];
						//
						if(u-1==0) maxx[u-1][g*2-1]++;
						
						g=g*2-1;
					}
					else if(maxx[u-1][g*2-1]<(1<<(u-1))){
						a[u-1][g*2-1]=a[u][g];
						//
						if(u-1==0) maxx[u-1][g*2-1]++;
						g=g*2-1;
					}
					else{
						a[u-1][g*2]=a[u][g];
						//
						if(u-1==0) maxx[u-1][g*2]++;
						g=g*2;
					}
				}
				else{
					if(a[u][g]>=l&&(maxx[u-1][g*2-1]<(1<<u))){
						a[u-1][g*2-1]=a[u][g];
						//
						if(u-1==0) maxx[u-1][g*2-1]++;
						g=g*2-1;
					}
					else if(a[u][g]>=r&&(maxx[u-1][g*2]<(1<<u))){
						a[u-1][g*2]=a[u][g];
						//
						if(u-1==0) maxx[u-1][g*2]++;
						g=g*2;
					}
					else{
						flag=1;
						cout<<"No Solution"<<endl;
						return 0;
					}
				}
				//g=g*2;
			}
		}
	}
	if(flag){
		cout<<"No Solution"<<endl;
	}
	else{
		for(int i=1;i<=(1<<n);i++){
			if(a[0][i]!=0)
			cout<<a[0][i]<<" ";
			else{
				cout<<ans<<" ";
			}
		}
		cout<<endl;
	}
	return 0;
}
