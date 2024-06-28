param N=6; #How many degrees we consider up to
var w1 >= 0;
var wk{i in 2..N} >=0 ; #k budget in graph with degree max i
var w_s >= 0;
# var alpha >= 0 ; #we can solve yes instance smaller than 0.718n, what's left are those bigger than 0.718n
var alpha{1..N} ; # alpha is alpha[1], and alpha_i is alpha[i]
param beta{2..N};
param gamma{2..N};
let beta[2]:=0;
let beta[3]:=(1/6);
let beta[4]:=(1/3);
let beta[5]:=(13/30);
let beta[6]:=(23/45);
let {i in 2..N} gamma[i] := beta[i]/(1-beta[i]);

var base;
param l; #lower bound of piece
param u; #upper bound of piece
param b_s=1-l;#budget on the independent set




var run_b = w1 + (sum{i in 2..N} wk[i]*(u-alpha[i])) + w_s * b_s; #branching algo when width based algo is not triggered
var run_w = 3^alpha[1]; #width based algo
var run;


minimize Obj: run;

subject to con_thre_ab_s_order_1{ i in 2..N}:
	alpha[i] <= min(alpha[i-1],(alpha[1]-beta[i])/(1-beta[i]));
	
subject to con_thre_ab_s_order_2:
	alpha[1] <= 1;

subject to alpha_u:
	alpha[1] <= u;

subject to run_time_con_1:
	run >= 2^run_b;
	
subject to run_time_con_2:
	run >= run_w;

subject to con_deg_above_N: # degree N+1=7+
	2^(-(
		w1
	)) + 2^(-(
		(N+2) * w1 + w_s + (sum{j in 2..N} gamma[j] * wk[j]) 
	)) <= 1;

subject to con_deg_i{i in 2..N}: # degree 2,3,4,5,6
	2^(-(
		w1 + (sum{j in i..N} wk[j])
	)) + 2^(-(
		(i+1) * w1 + (sum{j in i..N}  i * wk[j]) + (sum{j in 2..i-1} gamma[j] * wk[j]) + w_s 
	)) <= 1;
    
subject to con_deg_1: 
	2^(-(
		w1 + (sum{j in 2..N} wk[j])
	)) + 2^(-(
		2* w1 + (sum{j in 2..N} wk[j]) + w_s
	)) <= 1;
subject to con_deg_0: 
	2^(-(
		w1 + (sum{j in 2..N} wk[j])
	)) + 2^(-(
		w1 + w_s
	)) <= 1;