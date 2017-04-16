#include "deploy.h"
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <sstream>
#include <iostream>
#include <map>
#include <set>
using namespace std;
const int ESIZE = (1000*1000+500*2+1000*2+50)*2;
const int VSIZE = (5000+500+50);
const int INF = 199999999;
const int MXFLOW = 500*5000;
void dw(int &a,int b){ if ((b)< (a)) (a)=(b); }

struct Edge
{
	int from,to,cap,flow,cost;
	Edge(){}
};

struct User
{
	int no;
	int node;
	int flow;
};

struct Item
{
	int flow,cost,node;
	bool operator < (const Item& a) const
	{
		return flow*a.cost > cost*a.flow;
	}
};

Edge edges[ESIZE];
int G[VSIZE][VSIZE];
int newG[VSIZE][VSIZE];
Item best[VSIZE+5];
Edge eg[ESIZE+5];
User us[VSIZE+5];
int ntou[VSIZE+5];
int h = 0, nc, uc, ec, sc, links;
string str;
char strExt[100000];
const char *topo_file = NULL;
vector< map<int,int> > bestKeeper;
int svrLevel[VSIZE][2]; //0 maxFlow 1 hardware cost
int ntoLevel[VSIZE]; 
int ntoCost[VSIZE];
int levels = 0;
int startTime = 0;
int deployCost[VSIZE];
int runTime = 0;
int serverlevel[VSIZE] ;
set<string> ValSet ;
set<int> minCostSet ;
bool check = true ;


struct MCMF
{
	int n,m,s,t;
	int inq[VSIZE];
	int d[VSIZE];
	int p[VSIZE];
	int a[VSIZE];
	int slk[VSIZE];
	int ans;
	int flow;
	int S,T;
	bool vis[VSIZE];
	int servers[VSIZE]; //服务器以及它所跑的流量
	int select_server_level[VSIZE]; //选择的服务器以及它的规格


	void init(int n)
	{
		this->n = n;
		for(int i=0; i<n; i++) G[i][0] = servers[i] = select_server_level[i] = 0;
		m = 0;
		links = 0;
	}

	inline void AddEdge(int from, int to, int cap, int cost)
	{
		Edge &e = edges[m++];
		e.from = from;
		e.to = to;
		e.cap = cap;
		e.flow = 0;
		e.cost = cost;
		G[from][++G[from][0]] = m - 1;
		Edge &e1 = edges[m++];
		e1.from = to;
		e1.to = from;
		e1.cap = 0;
		e1.flow = 0;
		e1.cost = -cost;
		G[to][++G[to][0]] = m - 1;
		//cout<<"insert "<<from<<"->"<<to<<' '<<G[from][0]<<endl;
		//cout<<"insert "<<to<<"->"<<from<<' '<<G[to][0]<<endl;
	}

	int aug(int u,int f, int p, bool print = false)
	{
		// printf("u : %d , T : %d\n");
		// printf("u : %d , f : %d , p : %d\n",u,f,p);
		int t,left=f;
		if (u == T)
		{
			bestKeeper[p][d[S]] += f;
			ans+=f*(d[S]);
			flow += f; 
			servers[p] += f;
			//if(print)
			//	cout<<"ywz "<<p<<' '<<f<<' '<<servers[p]<<endl;
			return f;
		}
		vis[u]=1;
		for (int i = 1; i<=G[u][0]; ++i)
		{
			Edge& e = edges[G[u][i]];
			if (e.flow<e.cap && !vis[e.to])
			{
				t=d[e.to]+e.cost-d[u];
				if (t==0)
				{
					int delt=aug(e.to, e.cap - e.flow < left ? e.cap - e.flow : left, u,print);
					if (delt>0)
					{
						if(print)
						{
							if(e.flow < 0)
							{
								newG[e.to][e.from] -= delt; 
							}
							else
								newG[e.from][e.to] += delt;
						}
						edges[G[u][i]].flow += delt;
						edges[G[u][i]^1].flow -= delt;

						left-=delt;
					}
					if (left==0) 
						return f;
				}else 
					dw(slk[e.to],t);
			}
		}
		return f-left;
	}

	bool modlabel()
	{
		int delt=INF,i;
		for (i=0;i<n;i++)
			if (!vis[i]) { dw(delt,slk[i]);slk[i]=INF;}
		if (delt==INF) return true;
		for (i=0;i< n;i++)
			if (vis[i]) d[i]+=delt;
		return false;
	}



	inline int MinCost(int s, int t, bool print = false,bool findserverlevel = false)
	{
		++runTime;
		S = s;
		T = t;
		flow = ans=0;
		for (int i=0;i<n;i++) d[i]=0,slk[i]=INF;
		// printf("pass1\n");
		do{
			do {memset(vis,0,sizeof(vis));}while (aug(S, INF, -1, print));
			// printf("pass3\n");
		}while (!modlabel());
		// printf("pass2\n");
		
		for(int i=0; i<n; ++i)
		{
			if(servers[i] == 0)continue;
			int j = 0;
			while(svrLevel[j][0] < servers[i] && j < levels) ++j;
			ans += svrLevel[j][1] + deployCost[i];
			select_server_level[i] = j+1 ;
			if( findserverlevel ) 
			{
				// printf("---------------------\n");
				// printf("i : %d , j : %d \n",i,j);
				serverlevel[i] = j+1 ;
			}
		}
		if(print)cout<<h<<' '<<flow<<' '<<ans << ' '<<S<<' '<<T<<endl;
		if(flow < h)return INF;
		return ans;
	}




	int printWayPath(int u, int p, int a)
	{
		static int nd = 0;
		vis[u] = true;
		if(u == n-1){nd = p;return a;}
		for(int i=0; i<n; ++i)
		{
			if(!vis[i] && i != p && newG[u][i] > 0)
			{
				a = (a>newG[u][i])?newG[u][i]:a;
				a = printWayPath(i, u, a);
				newG[u][i] -= a;
				if(i!=n-1)
				{
					sprintf(strExt, "%d ", i);
					str += strExt;
					//cout<<i<<' ';
				}
				if(u == n-2)
				{
					// cout<<svrLevel[i][0]<<' '<<servers[nd]<<' '<<nd<<' '<<select_server_level[nd]-1<<endl;
					sprintf(strExt, "%d %d %d\n", ntou[i], a,  servers[nd]  );
					// cout << strExt << endl;
					str += strExt;
					//cout <<ntou[i]<<' '<<a<<'\n';
				}
				return a;
			}
		}
		return INF;
	}
	
	void display(int minCost)
	{
		// cout << "=============== display ============= " << endl;
		for(int i=0; i< nc; ++i)
		{
			int j = 0;
			while(svrLevel[j][0] < servers[i]) 
			{
				++j;
				// cout <<  "server[i] : " << servers[i]<< ",svrLevel : "<<svrLevel[j][0]<< " level : " <<j<<endl;
			}
			// cout << " end ... " << "server[i] : " << servers[i]<< ",svrLevel : "<<svrLevel[j][0]<< " level : " <<j<<endl;
			servers[i] = j;
		}
		if(false && minCost >= uc*sc)
		{
			links = uc;
			for(int i=0; i< uc; ++i)
			{
				sprintf(strExt, "%d %d %d ％d\n", us[i].node, us[i].no, us[i].flow);
				str += strExt;
			}
		}
		else
		{
			/*
			for(int i=0;i<nc+2;i++)
			{
				for(int j=0;j<nc+2; j++)
					cout<<newG[i][j]<<' ';
				cout<<endl;
			}
			*/
			links = 0;
			memset(vis, 0, sizeof(vis));
			while(printWayPath(nc, -1, INF) != INF)
			{
				links++;
				memset(vis, 0, sizeof(vis));
			}
			//printf("%d %d\n", minCost, uc*sc);
		}

		if(links == 0)
			topo_file = "NA";
		else
		{
			sprintf(strExt, "%d\n\n", links);
			str = strExt + str;
			strcpy(strExt, str.c_str());
			strExt[strlen(strExt)-1] = '\0';
			topo_file = strExt;
			// cout << topo_file << endl;
		}
	}
};

MCMF mcmf;

void init(char *s[MAX_EDGE_NUM], int lineNum)
{
	memset(ntoLevel, 0, sizeof(ntoLevel));
	memset(ntou, -1, sizeof(ntou));
	int u,v,c,f, i = 2, j = 0;
	sscanf(s[0],"%d%d%d", &nc, &ec, &uc);

	while(strlen(s[i]) > 2)
	{
		sscanf(s[i],"%d%d%d", &u, &f, &c);
		//printf("%d %d %d\n", u, f, c);
		svrLevel[u][0] = f;
		svrLevel[u][1] = c;
		++i, ++j;
	}
	levels = j;
	++ i;

	for( j=0; j<nc; ++i,++j)
	{
		sscanf(s[i],"%d%d", &u, &c);
		//printf("%d %d\n", u, c);
		deployCost[u] = c;
	}
	++i;

	//printf("%d %d %d\n\r\n%d\n\r\n", nc, ec, uc, sc);
	for( j=0; j<ec; ++i,++j)
	{
		sscanf(s[i],"%d%d%d%d", &u, &v, &c, &f);
		//printf("%d %d %d %d\n", u, v, c, f);
		eg[j].from = u;
		eg[j].to = v;
		eg[j].cap = c;
		eg[j].cost = f;
	}
	++i;

	for(j = 0; j<uc; ++i, ++j)
	{
		sscanf(s[i],"%d%d%d", &u, &v, &c);
		//printf("%d %d %d\n", u, v, c);
		us[j].no = u;
		us[j].node = v;
		us[j].flow = c;
		h += c;
		ntou[v] = u;
	}
	memset(newG, 0, sizeof(newG));
}

struct Statu
{
	int cost;
	string val;
	Statu():cost(0){val="";}
	Statu(int c, string v):cost(c),val(v){}
	bool operator < (const Statu& sta)const
	{
		return cost < sta.cost;
	}
};

struct GA
{
	static const int POPSZ = 15;
	int no;	
	Statu pop[POPSZ+5000];
	Statu child[POPSZ+5000];
	Statu best;
	int genes;	
	int startgs;
	double possible;
	int startGene[VSIZE];
	
	

	GA(){}
	inline double getpossible(int type)
	{
		double p ;
		if( type == 1 ) 
			p = possible ;
		else if( type == 2 )
			p = possible*10 ;
		else 
			p = possible*12 ;
		if(time(NULL) - startTime < 30)
			p = p*20 ;
		return p ;
	}

	void init(int gs, double p)
	{
		genes = gs;
		possible = p;
		no = 0;
		startgs = 0;
		for(int i=0; i<genes; ++i)
			startGene[i] = mcmf.select_server_level[i],startgs += ( mcmf.servers[i] > 0 ? 1 : 0 );
		int st = 4;	
		if(nc < 200)
			st = 7;	
		else if(nc < 500)
			st = 6;

		//cout<<"start:"<<endl;
		for(int i=0; i<st; ++i)
		{
			// printf(" ------------ init i : %d ------------ \n",i);
			int radCnt = 0;
			static char gene[VSIZE];
			for(int j=0; j<genes; ++j)gene[j] = '0';
			for(int j=0; j<genes; ++j)
			{
				if(startGene[j])
					gene[j] = startGene[j] -  0 + '0';
				else
					++radCnt;
			}
			if(i == 0)
			{
				gene[genes] = '\0';
				Statu sta(INF, string(gene));
				fitness(sta,"init1");
				//cout<<gene<<endl;
				best = sta;
				continue;
			}
			int setCnt = random()%3+1, location = 0;
			for(int j=0; j<setCnt && radCnt > 0; ++j)
			{
				location = random()%radCnt;	
				int zeroCnt = 0;
				for(int k=0; k<genes; ++k)
				{
					if(gene[k] == '0' && zeroCnt++ == location)
					{
						gene[k] = random()%levels  + '0' ;
					}
				}
				radCnt --;
			}
			gene[genes] = '\0';
			// cout<<gene<<endl;
			Statu sta(INF, string(gene));
			if(canTry(sta.val) && fitness(sta,"init2"))
			{
				update(sta,"init");

			}
		}
		cout<<"pop count: "<< no<<endl;

		//insert set
		
	}

	inline bool fitness(Statu& sta,string reason , bool print = false)
	{
		// cout << "fitness start .." << endl;
		mcmf.init(nc+2);
		for(int i=0; i<ec; ++i)
		{
			mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
			mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
		}
		for(int i=0; i<uc; ++i)
		{
			mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
		}
		// printf("fitness : \n");
		for(int i=0; i<genes; ++i)
		{
			if(sta.val[i] != '0')
			{
				int templevel = (sta.val[i]-'0');
				int edgeflow = svrLevel[ templevel-1 ][0] ;
				mcmf.AddEdge(i, nc+1, edgeflow , 0);
					
			}
				
		}
		int minCost = INF;
		minCost = mcmf.MinCost(nc, nc+1, print);
		if(print)
		{
			printf("============ end GA ==========\n");
			int endservernum = 0 ;
			for( int i = 0 ; i<genes ; i++ )
				if( mcmf.servers[i] != 0) 
					endservernum++ ;
			printf("end server num is : %d\n",endservernum);
		}
		if(print)mcmf.display(minCost);
		// cout << "mincost : " << minCost << endl;
		if(minCost == INF)return false;
		sta.cost = minCost;
		if(print)cout<<minCost<<endl;
		//跑完之后更新服务器部署情况
		for( int i = 0 ; i <genes ; i++ )
		{
			sta.val[i] = mcmf.select_server_level[i] + '0' ;
		}

		return true;
	}
	
	inline void selection(int& p1, int& p2)
	{
		p2 = roulettewheel();
		// do
		// {
		// 	p1 = roulettewheel();	
		// 	p2 = roulettewheel();	
		// }while(p1 == p2);
	}

	inline int roulettewheel()
	{
		double pm = random()%10000/10000.0;
		double add = 0, total = 0;
		for(int i=0; i<no; ++i)
			total += (2*best.cost - pop[i].cost > 0 ? 2*best.cost - pop[i].cost : 0);
		for(int i=0; i<no; ++i)
		{
			add += (2*best.cost - pop[i].cost > 0 ? 2*best.cost - pop[i].cost : 0);
			if(add/total > pm)
				return i;
		}
		return no - 1;
	}

	inline void update(Statu& sta,string msg)
	{
		canTry(sta.val);

		if(no < POPSZ)
		{
			pop[no++] = sta;
			if(best.cost > sta.cost)
			{
				// cout << " ============ " << msg <<  " ============ " << "best : " << best.cost <<  endl;
				best = sta;
			}
				
			return;
		}
		int j = 0, an = 0;
		for(int i = 0; i<no; ++i)
			if(an < pop[i].cost)
				an = pop[i].cost, j = i;
		if(pop[j].cost >= sta.cost)
		{
			// cout << " ============ " << msg <<  " ============ " << "change pop : " << sta.cost <<  endl;
			// cout << sta.val << endl;
			pop[j] = sta;
		}
		if(best.cost > sta.cost)
		{
			// cout << " ============ " << msg <<  " ============ " << "best : " << best.cost <<  endl;
			best = sta;
		}
			
		ValSet.insert(sta.val);
	}

	inline bool canTry(string& gene)
	{
		// printf(" ============= check canTry ============\n");
		// for(int i=0; i<no; ++i)
		// 	if(gene == pop[i].val)
		// 	{
		// 		return false;
		// 	}
		set<string>::iterator it = ValSet.find(gene) ;
		if( it != ValSet.end()  )
		{
			return false ;
		}
		// ValSet.insert(gene);
			
		
		int setCnt = 0,tmpsumflow = 0 ;
		for(int i=0; i<(int)gene.size(); ++i)
		{
			if(gene[i] != '0')
			{
				++ setCnt;
				// svrLevel
				tmpsumflow += svrLevel[ gene[i] - '0' - 1 ][0] ;
			}
		}

		//check server flow if is fit
		// cout << "tmpsumflow : " << tmpsumflow << " , h " << h << endl;
		// cout << "setcnt : " << setCnt << " , startgs : " << startgs << endl;
		if(setCnt < startgs - 2 || setCnt>uc || setCnt == 0 || tmpsumflow < h )return false;
		return true;
	}

	inline void crossover(int p1, int p2)
	{
		int index = random()%genes;
		// string s1 = pop[p1].val;
		string s1 = best.val ;
		string s2 = pop[p2].val;
		string tmp1 = s1.substr(0, index) + s2.substr(index, genes-index);
		string tmp2 = s2.substr(0, index) + s1.substr(index, genes-index);
		Statu po1(INF, tmp1), po2(INF, tmp2);
		if(canTry(po1.val) && fitness(po1,"crossovver"))
			update(po1,"crossover");
		if(canTry(po2.val) && fitness(po2,"crossover"))
			update(po2,"crossover");
	}

	//对最优解进行变异
	inline void mutation2()
	{	 
		for(int j=0; j<genes ; ++j)
		{
			double p = random()%10000/10000.0;
			if(p < getpossible(2))// && (tmp[j] != best.val[j] || best.val[j] != '1'))
			{
				int possb = j;
				Statu tmp = best ;
				if( tmp.val[possb] != '0' )
				{
					tmp.val[possb] = '0' ;
				}
				Statu sta(INF, tmp.val );
				if( canTry(tmp.val) && fitness(sta,"mutation2") )
				{
					// printf("mutation2\n");
					update(sta,"mutation2");
				}
			}
		}
	}

	//减少一个服务器数量
	void mutation4()
	{
		int ss[VSIZE] ;
		for(int i=0; i<nc; ++i)
			ss[i] = best.val[i] - '0';
		int  possb = 0 ;
		
		int genesize = 0 ;
		vector<int> possible1;
		for(int j=0; j<nc; ++j)
		{
			if(best.val[j] != '0')
			{
				possible1.push_back(j);
				genesize++ ;
			}
				
		}
		int id = random()%genesize ;
		Statu tmp = best ;
		for(int j=0; j<genesize; ++j)
		{
			if( j == id )
			{
				tmp.val[possible1[j]] = '0' ;
			}
			else 
			{
				tmp.val[possible1[j]] = levels - 1 + '0' ;
			} 
		}
		Statu sta(INF, tmp.val );
		if( canTry(tmp.val) && fitness(sta,"mutation4") )
		{
			update(sta,"mutation4");
		}


	}

	void mutation3()
	{
		int ss[VSIZE] ;
		for(int i=0; i<nc; ++i)
			ss[i] = best.val[i] - '0';
		int  possb = 0 ;
		
		vector<int> possible1;
		for(int j=0; j<nc; ++j)
		{
			if(best.val[j] != '0')
				possible1.push_back(j);
		}
		for(int j=0; j<(int)possible1.size(); ++j)
		{

			double p = random()%10000/10000.0;
			if(p < getpossible(3) )// && (tmp[j] != best.val[j] || best.val[j] != '1'))
			{
				possb = possible1[j];
				Statu tmp = best ;
				if( tmp.val[possb] != '0' )
				{
					int index = random()%genes ;
					char tmpindex = tmp.val[possb] ;
					tmp.val[possb] = tmp.val[index] ;
					tmp.val[index] = tmpindex ; 
				}
				
				Statu sta(INF, tmp.val );
				if( canTry(tmp.val) && fitness(sta,"mutation3") )
				{
					// printf("mutation3\n");
					update(sta,"mutation3");
				}
			}
		}
	}

	inline void mutation()
	{
		for(int i=0; i<no; ++i)
		{

			bool flag = false;
			string tmp = pop[i].val;
			int cnt = 0 ;
			for(int j=0; j<genes; ++j)
			{
				int cnt = 0 ;
				double p = random()%10000/10000.0;
				if(p < getpossible(1))// && (tmp[j] != best.val[j] || best.val[j] != '1'))
				{
					tmp[j] = random()%levels + '0' ;
					// int p2 = random()%2 ;
					// if( p2 % 2 == 0 )
					// {
					// 	tmp[j] = random()%levels + '0' ;
					// }
					// else 
					// {
					// 	int tempindex = random() % genes ;
					// 	char tmpindex = tmp[tempindex] ;
					// 	tmp[tempindex] = tmp[j] ;
					// 	tmp[j] = tmpindex ; 
					// }
					// if( tmp[j] < '0' )
					// 	cout << "mutation ... edge .. error" << endl;
					flag = true;

				}


			}
			if(flag)
			{
				cnt++ ;
				Statu sta(INF, tmp);

				if(canTry(tmp) && fitness(sta,"mutation"))
				{
					update(sta,"mutation");
				}
				flag = false ;
				if( cnt > 2 )
					break ;
			}

		}
		//for(int i=0; i<chno; ++i)
		//	update(child[i]);
	}

	inline void dispose(int n)
	{
		int i=0;
		for(; i<n; ++i)
		{

			//sort(pop,pop+no);
			// cout<<"NO: "<<i<<endl;
			//cout<<"people: "<<no<<endl;
			evolution();
			/*
			if(best.cost != anwser)
			{
				anwser = best.cost;
				findCnt = 0;
			}
			++ findCnt;
			if(findCnt > 8000)
				break;
				*/
			// cout << "csx : " << best.cost << endl;
			if(time(NULL) - startTime > 85)
				break;
		}
		// cout<<"around: "<<i<<endl;
	}
	
	inline void evolution()
	{

		int p1, p2;
		if( time(NULL) - startTime > 20 )
		{
			for(int i = 0 ; i<10 ; i++ )
			{
				selection(p1, p2);
				crossover(p1, p2);
			}
			int tt = random()%30;
			if( tt == 0)
				mutation();
			// mutation2(); 
			mutation3();
			// mutation4();

		}
		else 
		{
			selection(p1, p2);
			crossover(p1, p2);
			mutation();
			// mutation2(); 
			mutation3();
			// mutation4();
		}


	}

};

void getBestWays()
{
	startTime = time(NULL);
	for(int i=0; i<nc+2; ++i)
	{
		best[i].flow = 0;
		best[i].cost = 1;
		best[i].node = i;
		bestKeeper.push_back(map<int, int>());
	}
	for(int i=0; i<nc; ++i)
	{
		mcmf.init(nc+1);
		for(int i=0; i<ec; ++i)
		{
			mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
			mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
		}
		for(int i=0; i<uc; ++i)
		{
			mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
		}
		mcmf.AddEdge(i,nc+1 , INF , 0 );
		mcmf.MinCost(nc, nc+1,false ,true);	
	}
	
	for(int i=0; i<nc;  ++i)
	{
		int flow = 0, cost = 0 ;
		for(map<int,int>::iterator it = bestKeeper[i].begin(); it != bestKeeper[i].end(); ++it)
		{
			flow += it->second;
			cost += it->first * it->second;
			
			int j = 0;
			while(svrLevel[j][0] < flow && j<levels) ++j;
			if(j==levels)break;
			if(best[i].flow * (svrLevel[j][1]+cost+deployCost[i]) < flow * best[i].cost)		
			{
				//cout<<i<<' '<<it->first<<' '<< it->second<<' '<<flow<<' '<<cost + sc<<endl;
				best[i].flow = flow;
				best[i].cost = cost + svrLevel[j][1] + deployCost[i];
				ntoLevel[i] = j;
				//ntoCost[i] = (int)(svrLevel[j][1] + deployCost[i])/flow;
			}	
		}
		//cout<<ntoCost[i]<<' ';
	}
	cout<<endl;
	sort(best, best+nc);
	
	// printf(" ========== best ======= \n");
	vector<int> src;
	int sum = 0;
	for(int i=0; i<nc && sum<h; ++i)
	{
		// printf("%d/%d %d\n", best[i].flow, best[i].cost, best[i].node);
		sum += best[i].flow;
		src.push_back(best[i].node);
	} 
	mcmf.init(nc+2);
	for(int i=0; i<ec; ++i)
	{
		mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
		mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
	}
	for(int i=0; i<uc; ++i)
	{
		mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
	}
	for(int i=0; i<(int)src.size(); ++i)
	{
		mcmf.AddEdge(src[i], nc+1, svrLevel[ntoLevel[src[i]]][0], 0);
	}
	mcmf.MinCost(nc, nc+1);
	// printf("first mcmf : %d\n",tmp1);
	for(int i=1;i<G[nc][0]; ++i)
	{
		Edge &e = edges[G[nc][i]];
		if(e.flow < e.cap)
		{
			if(find(src.begin(), src.end(),e.to) == src.end())
			{
				src.push_back(e.to);
			}
		}
	}
	mcmf.init(nc+2);
	for(int i=0; i<ec; ++i)
	{
		mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
		mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
	}
	for(int i=0; i<uc; ++i)
	{
		mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
	}
	
	for(int i=0; i<(int)src.size(); ++i)
	{
		mcmf.AddEdge(src[i], nc+1, svrLevel[ntoLevel[src[i]]][0], 0);
	}
	int minCost = INF;
	minCost = mcmf.MinCost(nc, nc+1);
	// printf("second mcmf : %d\n",tmp2);
	// cout<<"ywz "<<minCost<<' '<< svrLevel[levels-1][0] << ' '<<levels<<endl;

	// printf("=================== change the server =============\n");
	int ss[VSIZE],ss2[VSIZE];
	for(int i=0; i<nc; ++i)
		ss[i] = mcmf.servers[i];
	int flag = true ;
	int second = minCost, possb = 0, k = 0;
	{
		vector<int> possible;
		possible.clear();
		
		for(int j=0; j<nc; ++j)
		{
			if(mcmf.servers[j] != 0)
				possible.push_back(j);
		}
		for(int j=0; j<(int)possible.size(); ++j)
		{
			possb = possible[j];
			mcmf.init(nc+2);
			for(int i=0; i<ec; ++i)
			{
				mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
				mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
			}
			for(int i=0; i<uc; ++i)
			{
				mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
			}
			for(int i=0; i<(int)src.size(); ++i)
			{
				//为了产生更多的可行解，但是担心少了一个点之后会容纳流量，所以让服务器档次提升到最高。
				if(src[i] != possb && src[i] != -1)
					mcmf.AddEdge(src[i], nc+1, svrLevel[ levels-1 ][0], 0);
					// mcmf.AddEdge(src[i], nc+1, svrLevel[ serverlevel[ src[i] ] ][0], 0);
					// mcmf.AddEdge(src[i], nc+1, svrLevel[ntoLevel[src[i]]][0], 0);
				if(src[i] == possb)
					k = i;
			}
			int tmp = mcmf.MinCost(nc, nc+1);
			// printf("tmp : %d\n",tmp);
			if(tmp < second)
			{
				flag = false ;
				second = tmp;
				src[k] = -1;
				for(int i=0; i<nc; ++i)
				{
					ss[i] = mcmf.servers[i];
					ss2[i] = mcmf.select_server_level[i] ;
				}
			}
		}
	}
	if( !flag )
	{
		for(int i=0; i<nc; ++i)
		{
			mcmf.servers[i] = ss[i];
			mcmf.select_server_level[i] = ss2[i] ;
		}
	}

	printf(" =================== before GA algorithm ===================\n");
	int initservernum = 0 ;
	for( int i = 0 ; i<nc ; i++ )
		if( mcmf.servers[i] != 0 )
			initservernum++ ;
	printf("server num : %d\n",initservernum);

	printf(" ================= start GA algorithm =================\n");
	printf("start mcmf's cost : %d\n",second);
	GA ga;
	ga.init(nc, 0.082);
	ga.dispose(200000);
	ga.fitness(ga.best, "end",true);
	// // cout<<"runTime "<< runTime<<endl;
}


//你要完成的功能总入口
void deploy_server(char * topo[MAX_EDGE_NUM], int line_num,char * filename)
{

	// 需要输出的内容
	// char * topo_file = (char *)"17\n\n0 8 0 20\n21 8 0 20\n9 11 1 13\n21 22 2 20\n23 22 2 8\n1 3 3 11\n24 3 3 17\n27 3 3 26\n24 3 3 10\n18 17 4 11\n1 19 5 26\n1 16 6 15\n15 13 7 13\n4 5 8 18\n2 25 9 15\n0 7 10 10\n23 24 11 23";
	init(topo, line_num);
	getBestWays();
	// 直接调用输出文件的方法输出到指定文件中(ps请注意格式的正确性，如果有解，第一行只有一个数据；第二行为空；第三行开始才是具体的数据，数据之间用一个空格分隔开)
	
	write_result(topo_file, filename);
}
