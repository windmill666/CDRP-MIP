/*********************************************
 * OPL 12.9.0.0 Model
 * Author: lizongheng
 * Creation Date: 2020��2��6�� at ����3:16:33
 *********************************************/
/**
 * ģ�͵ĳ�ʼ����
 */
int B = ...;//��װ����ܸ������Ѷ��ںͶѶ���ļ�װ��֮��
int H = ...;//�Ѷ�ĸ߶�����
int S = ...;//�Ѷ�Ŀ������
int T_upper = ...;//�����������Ͻ�
int T_lower = ...;//�����������½�
int Br = ...;//�Ѷ���Ҫȡ�ļ�װ�����
int Bs = ...;//�Ѷ���Ҫ��ļ�װ�����
int B_R[1..Br] = ...;//�Ѷ���Ҫȡ�ļ�װ�伯��
int N_B_R[1..(B-Br)] = ...;//
int B_S[1..Bs] = ...;//�Ѷ���Ҫ��ļ�װ�伯��
int N_B_S[1..(B-Bs)] = ...;//
int C[1..B][1..B+1] = ...;//��װ���ʼ�����λ����Ϣ
/**
 * ģ�͵ľ��߱���
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
 * ģ�͵�Ŀ�꺯��
 */
minimize sum(i in I,j in J:j!=i,t in T) yd[i][j][t];
/**
 * ģ�͵�Լ��
 */
 subject to{
 	//(i)���ڼ�װ��λ����Ϣ��Լ��
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
 	//(ii)��������(lift-up)������Լ��
 	forall(t in T:t<=T_lower)
 	  sum(i in I,j in J:j!=i) yd[i][j][t] == 1;
 	forall(t in T:t>T_lower)
 	  sum(i in I,j in J:j!=i) yd[i][j][t] <= sum(i in I,j in J:j!=i) yd[i][j][t-1];
 	forall(i in I,j in J:j!=i,t in T)
 	  yd[i][j][t] <= x[i][j][t-1];
 	forall(i in I,t in T)
 	  sum(j in J:j!=i) yd[i][j][t] <= sum(j in J:j!=i) x[i][j][t-1] - sum(j in I:j!=i) x[j][i][t-1];
 	//(iii)���ڷ���(lift-down)������Լ��
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
 	//(iv)����ȡ��(retrieval)������Լ��
	forall(k in 1..(B-Br),j in J:j!=N_B_R[k],t in T)
	  zd[N_B_R[k]][j][t] == 0;
 	forall(k in 1..Br,t in T)
 	  sum(j in J:j>B_R[k]) zd[B_R[k]][j][t] <= (sum(j in J:j!=B_R[k]) x[B_R[k]][j][t-1])
 	     - sum(i in I:i>B_R[k]) (x[i][B_R[k]][t-1]-yd[i][B_R[k]][t]+yp[i][B_R[k]][t]);
 	forall(k in 1..Br,t in T)
 	  sum(j in J:j>B_R[k]) zd[B_R[k]][j][t] <= sum(i in I,j in J:j!=i) yd[i][j][t];
 	
 	forall(k in 2..Br,t in T)
 	  sum(j in J:j>B_R[k],t_temp in T:t_temp<=t) zd[B_R[k]][j][t_temp] <= sum(j in J:j>B_R[k-1],t_temp in T:t_temp<=t) zd[B_R[k-1]][j][t_temp];
 	//(v)���ڴ��䶯����Լ��
 	forall(k in 1..(B-Bs),j in J:j!=N_B_S[k],t in T)
	  zp[N_B_S[k]][j][t] == 0;
	// ������4��7�ϣ�7��4�ϵ��߼�����
// 	forall(k in 1..Bs,j in 1..Bs:B_S[j]!=B_S[k],t in T)
// 	  zp[B_S[k]][B_S[j]][t] + zp[B_S[j]][B_S[k]][t] <= 1;
 	// �����turn�Ĳ���
 	forall(k in 1..Bs,t in T)
 	  sum(j in J:j!=B_S[k]) zp[B_S[k]][j][t] <= sum(i in I,j in J:j!=i) yd[i][j][t];	  
 	  
 	// ---����˳������ƿ�ʼ
 	// ��ͬturn�Ĵ���˳������
 	forall(k in 2..Bs,t in T)
 	  sum(j in J:j!=B_S[k],t_temp in T:t_temp<=t) zp[B_S[k]][j][t_temp] <= sum(j in J:j!=B_S[k-1],t_temp in T:t_temp<=t) zp[B_S[k-1]][j][t_temp];	
 	
 	// ������߼�˳�����ƣ������10������Ҫ�棬����Ҫ9+8+7+6+5+4+3+2+1��Լ��
 	// ������߼�˳�����ƣ������3������Ҫ�棬����Ҫ2+1��Լ��
 	forall(t in T)
 	  zp[B_S[1]][B_S[2]][t] == 0;// ��һ�����Ӵ����ʱ�򣬺��ʣ������ӻ�δ���⣬���Բ����ܴ��������棬�Դ�����
 	forall(t in T)
 	  zp[B_S[1]][B_S[3]][t] == 0;// ��һ�����Ӵ����ʱ�򣬺��ʣ������ӻ�δ���⣬���Բ����ܴ��������棬�Դ�����
 	forall(t in T)
 	  zp[B_S[2]][B_S[3]][t] == 0;// ��һ�����Ӵ����ʱ�򣬺��ʣ������ӻ�δ���⣬���Բ����ܴ��������棬�Դ�����
 	// ---����˳�����ƽ���
 	
 	// ���䶯��������ȡ����֮����
 	forall(t in T)
 	  sum(j in J:j!=B_S[1],t_temp in T:t_temp<=t) zp[B_S[1]][j][t_temp] <= sum(j in J:j>B_R[Br],t_temp in T:t_temp<=t) zd[B_R[Br]][j][t_temp];
 	// ǿ�ƽ��д��䣬����������費���䣬�����߼�����
 	// ����������ڶѶ��⼯װ��ĸ���
 	sum(k in 1..Bs,j in J:j!=B_S[k],t in T) zp[B_S[k]][j][t] == Bs;
 	
 	// ���䲻���ص�
 	forall(j in J,t in T)
 	  sum(k in 1..Bs) zp[B_S[k]][j][t] <= 1;

	// �����ڵ�������ƣ����ܳ���S��
 	forall(t in T)
 	  sum(k in 1..Bs) zp[B_S[k]][B+1][t] <= S - sum(i in I) (x[i][B+1][t-1] - yd[i][B+1][t] + yp[i][B+1][t] - zd[i][B+1][t]);
 	
 	//(vi)���ڸ߶����Ƶ�Լ��
	forall(i in I,t in T)
	  u[i][t] <= H-1;
	forall(i in I,j in I:j!=i,t in T)
	  u[i][t] >= u[j][t] + 1 - H*(1 - x[i][j][t]);
	  
	//(vii)����BP block������Լ��
	forall(i in I)
	  q[i][T_upper+1] <= sum(j in J:j<i) p[i][j];
	forall(i in I)
	  q[i][T_upper+1] >= (sum(j in J:j<i) p[i][j])/20;
	sum(i in I) q[i][T_upper+1] <= 0;
}