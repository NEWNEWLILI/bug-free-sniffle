#include <iostream>
#include <bits/stdc++.h>
using namespace std;
#define int long long
#define N 550000
int a[N];
signed main(){
	int a,b,n;
	cin>>a>>b>>n;
	if(a==0&&b==0){
        cout<<n<<" 0"<<endl;
		return 0;
	}
	else if(a==0){
		if(b%n==0){
			cout<<"0 "<<n<<endl;
		}
		else{
			cout<<"No Solution"<<endl;
		} 
		return 0;
	}
	else if(b==0){
		if(a%n==0){
			cout<<n<<" 0"<<endl;
		}
		else{
			cout<<"No Solution"<<endl;
		} 
		return 0;
	}
	int x=-1,y=-1,op=-1;
	for(int i=1;i<n;i++){
		if((a%i==0)&&(b%(n-i)==0)){
			int cha=abs(a/i-(b/(n-i)));
			if(op==-1){
				op=cha;
				x=i,y=n-i;
			}
			else{
				if(cha<op){
					x=i;y=n-i;
					op=cha;
				}
			}
		}
	}
	if(op==-1){
		cout<<"No Solution"<<endl;
		
	}
	else{
		cout<<x<<" "<<y<<endl;
	}
	return 0;
}
