/*********************************************
 * OPL 12.9.0.0 Model
 * Author: lizongheng
 * Creation Date: 2020年2月6日 at 下午3:16:33
 *********************************************/
/**
 * 模型的初始输入
 */
int B = ...;//集装箱的总个数：堆垛内和堆垛外的集装箱之和
int H = ...;//堆垛的高度限制
int S = ...;//堆垛的宽度限制
int T_upper = ...;//翻倒次数的上界
int T_lower = ...;//翻倒次数的下界
int Br = ...;//堆垛内要取的集装箱个数
int Bs = ...;//堆垛外要存的集装箱个数
int B_R[1..Br] = ...;//堆垛内要取的集装箱集合
int N_B_R[1..(B-Br)] = ...;//
int B_S[1..Bs] = ...;//堆垛外要存的集装箱集合
int N_B_S[1..(B-Bs)] = ...;//
int C[1..B][1..B+1] = ...;//集装箱初始的相对位置信息
/**
 * 模型的决策变量
 */
range I = 1..B;
range J = 1..B+1;
range T = 2..T_upper+1;
range T_0= 1..T_upper+1;
dvar int x[I][J][T_0] in 0..1;
dvar int p[I][J] in 0..1;
dvar int yd[I][J][T] in 0..1;
dvar int yp[I][J][T] in 0..1;
dvar int zd[I][J][T] in 0..1;
dvar int zp[I][J][T] in 0..1;
dvar int w2[I][J][I] in 0..1;
dvar int w[I][J][J][J] in 0..1;
dvar int q[I][T] in 0..1;
dvar int+ u[I][T];
/**
 * 模型的目标函数
 */
minimize sum(i in I,j in J:j!=i,t in T) yd[i][j][t];
/**
 * 模型的约束
 */
 subject to{
 	//(i)关于集装箱位置信息的约束
 	forall(i in I,j in J:j!=i)
 	  x[i][j][1] == C[i][j];
 	forall(i in I,j in J:j!=i,t in T)
 	  x[i][j][t] == x[i][j][t-1] - yd[i][j][t] + yp[i][j][t] - zd[i][j][t] + zp[i][j][t];	  
 	forall(i in I,j in I:j!=i,k in I:k!=i&&k!=j){
	  w2[i][k][j] >= x[i][k][T_upper+1] + x[k][j][T_upper+1] -1;
	  w2[i][k][j] <= x[i][k][T_upper+1];
	  w2[i][k][j] <= x[k][j][T_upper+1];
	}
// 	forall(i in I,j in J:j!=i,k1 in I:k1!=i&&k1!=j,k2 in I:k2!=i&&k2!=j&&k2!=k1){
//	  w[i][k1][k2][j] >= x[i][k1][T_upper+1] + x[k1][k2][T_upper+1] + x[k2][j][T_upper+1] - 2;
//	  w[i][k1][k2][j] <= x[i][k1][T_upper+1];
//	  w[i][k1][k2][j] <= x[k1][k2][T_upper+1];
//	  w[i][k1][k2][j] <= x[k2][j][T_upper+1];
//	}
 	forall(i in I,j in I:j!=i)
 	  p[i][j] == x[i][j][T_upper+1] + sum(k in I:k!=i&&k!=j) w2[i][k][j];// + sum(k1 in I:k1!=i&&k1!=j,k2 in I:k2!=i&&k2!=j&&k2!=k1) w[i][k1][k2][j];
 	//(ii)关于提箱(lift-up)动作的约束
 	forall(t in T:t<=T_lower)
 	  sum(i in I,j in J:j!=i) yd[i][j][t] == 1;
 	forall(t in T:t>T_lower)
 	  sum(i in I,j in J:j!=i) yd[i][j][t] <= sum(i in I,j in J:j!=i) yd[i][j][t-1];
 	forall(i in I,j in J:j!=i,t in T)
 	  yd[i][j][t] <= x[i][j][t-1];
 	forall(i in I,t in T)
 	  sum(j in J:j!=i) yd[i][j][t] <= sum(j in J:j!=i) x[i][j][t-1] - sum(j in I:j!=i) x[j][i][t-1];
 	//(iii)关于放箱(lift-down)动作的约束
 	forall(t in T:t<=T_lower)
 	  sum(i in I,j in J:j!=i) yp[i][j][t] == 1;
 	forall(t in T:t>T_lower)
 	  sum(i in I,j in J:j!=i) yp[i][j][t] <= sum(i in I,j in J:j!=i) yp[i][j][t-1];
 	forall(i in I,t in T)
 	  sum(j in J:j!=i) yp[i][j][t] == sum(j in J:j!=i) yd[i][j][t];
 	forall(j in J,t in T)
 	  sum(i in I:i!=j) yp[i][j][t] <= 1 - sum(i in I:i!=j) yd[i][j][t];
 	forall(j in I,t in T)
 	  sum(i in I:i!=j) yp[i][j][t] <= sum(i in J:i!=j) x[j][i][t-1] - sum(i in I:i!=j) x[i][j][t-1];
 	forall(t in T)
 	  sum(i in I) yp[i][B+1][t] <= S - sum(i in I) x[i][B+1][t-1];
 	//(iv)关于取箱(retrieval)动作的约束
	forall(k in 1..(B-Br),j in J:j!=N_B_R[k],t in T)
	  zd[N_B_R[k]][j][t] == 0;
 	forall(k in 1..Br,t in T)
 	  sum(j in J:j>B_R[k]) zd[B_R[k]][j][t] <= (sum(j in J:j!=B_R[k]) x[B_R[k]][j][t-1])
 	     - sum(i in I:i>B_R[k]) (x[i][B_R[k]][t-1]-yd[i][B_R[k]][t]+yp[i][B_R[k]][t]);
 	forall(k in 1..Br,t in T)
 	  sum(j in J:j>B_R[k]) zd[B_R[k]][j][t] <= sum(i in I,j in J:j!=i) yd[i][j][t];
 	
 	forall(k in 2..Br,t in T)
 	  sum(j in J:j>B_R[k],t_temp in T:t_temp<=t) zd[B_R[k]][j][t_temp] <= sum(j in J:j>B_R[k-1],t_temp in T:t_temp<=t) zd[B_R[k-1]][j][t_temp];
 	//(v)关于存箱动作的约束
 	forall(k in 1..(B-Bs),j in J:j!=N_B_S[k],t in T)
	  zp[N_B_S[k]][j][t] == 0;
	// 不允许4在7上，7在4上的逻辑错误
// 	forall(k in 1..Bs,j in 1..Bs:B_S[j]!=B_S[k],t in T)
// 	  zp[B_S[k]][B_S[j]][t] + zp[B_S[j]][B_S[k]][t] <= 1;
 	// 避免空turn的产生
 	forall(k in 1..Bs,t in T)
 	  sum(j in J:j!=B_S[k]) zp[B_S[k]][j][t] <= sum(i in I,j in J:j!=i) yd[i][j][t];	  
 	  
 	// ---存箱顺序的限制开始
 	// 不同turn的存箱顺序限制
 	forall(k in 2..Bs,t in T)
 	  sum(j in J:j!=B_S[k],t_temp in T:t_temp<=t) zp[B_S[k]][j][t_temp] <= sum(j in J:j!=B_S[k-1],t_temp in T:t_temp<=t) zp[B_S[k-1]][j][t_temp];	
 	
 	// 存箱的逻辑顺序限制，如果有10个箱子要存，则需要9+8+7+6+5+4+3+2+1个约束
 	// 存箱的逻辑顺序限制，如果有3个箱子要存，则需要2+1个约束
 	forall(t in T)
 	  zp[B_S[1]][B_S[2]][t] == 0;// 第一个箱子存入的时候，后边剩余的箱子还未进垛，所以不可能存在其上面，以此类推
 	forall(t in T)
 	  zp[B_S[1]][B_S[3]][t] == 0;// 第一个箱子存入的时候，后边剩余的箱子还未进垛，所以不可能存在其上面，以此类推
 	forall(t in T)
 	  zp[B_S[2]][B_S[3]][t] == 0;// 第一个箱子存入的时候，后边剩余的箱子还未进垛，所以不可能存在其上面，以此类推
 	// ---存箱顺序限制结束
 	
 	// 存箱动作必须在取完箱之后发生
 	forall(t in T)
 	  sum(j in J:j!=B_S[1],t_temp in T:t_temp<=t) zp[B_S[1]][j][t_temp] <= sum(j in J:j>B_R[Br],t_temp in T:t_temp<=t) zd[B_R[Br]][j][t_temp];
 	// 强制进行存箱，否则程序懒惰不存箱，陷入逻辑错误
 	// 存箱次数等于堆垛外集装箱的个数
 	sum(k in 1..Bs,j in J:j!=B_S[k],t in T) zp[B_S[k]][j][t] == Bs;
 	
 	// 存箱不可重叠
 	forall(j in J,t in T)
 	  sum(k in 1..Bs) zp[B_S[k]][j][t] <= 1;

	// 存箱在地面的限制，不能超过S列
 	forall(t in T)
 	  sum(k in 1..Bs) zp[B_S[k]][B+1][t] <= S - sum(i in I) (x[i][B+1][t-1] - yd[i][B+1][t] + yp[i][B+1][t] - zd[i][B+1][t]);
 	
 	//(vi)关于高度限制的约束
	forall(i in I,t in T)
	  u[i][t] <= H-1;
	forall(i in I,j in I:j!=i,t in T)
	  u[i][t] >= u[j][t] + 1 - H*(1 - x[i][j][t]);
	  
	//(vii)关于BP block数量的约束
	forall(i in I)
	  q[i][T_upper+1] <= sum(j in J:j<i) p[i][j];
	forall(i in I)
	  q[i][T_upper+1] >= (sum(j in J:j<i) p[i][j])/20;
	sum(i in I) q[i][T_upper+1] <= 0;
}