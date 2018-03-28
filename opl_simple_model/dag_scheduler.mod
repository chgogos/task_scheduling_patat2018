using CP;

int T = ...; // number of tasks
int P = ...; // number of processors
int E = ...; // number of edges
int V = ...; // number of data objects

tuple arc { int node1; int node2;};

tuple var_req {
	int task_id;	// task that uses the data object
	int var_freq;	// frequency of accesses to the data object 
	int gain;		// gain, total gain = var_freq * gain
	int attr;		// 1 = read the data object, 2 = modify the data object
	int var_id;		// data object id
}

// task execution time on each processors when all data objects are in main memory
int Exec[t in 1..T][p in 1..P] = ...;

arc Edges[e in 1..E] = ...;	// edges as defined at the DAG

int VarS[v in 1..V] = ...; 	// the size of each data object

{var_req} VarR = ...;		// usage details of data objects by the tasks 

int SPMS[p in 1..P] = ...; 	// scratchpad size per processor

// convenience data structures  
{int} StartAfter[1..T] = ...; // tasks that start after each task
{int} VarsThatTaskUses[t in 1..T] = {r.var_id | r in VarR: r.task_id == t}; 
{int} VarsThatTaskModify[t in 1..T] = {r.var_id | r in VarR: r.task_id == t && r.attr == 2}; 
{int} TasksUsingVar[v in 1..V] = {r.task_id | r in VarR: r.var_id == v}; 

// Variables
dvar interval task_iv[t in 1..T];

dvar interval task_oiv[t in 1..T][p in 1..P] optional;

dvar interval load_iv[t in 1..T];

dvar interval store_iv[t in 1..T];

dvar int load_b[t in 1..T][v in 1..V] in 0..1;

dvar int store_b[t in 1..T][v in 1..V] in 0..1;

dvar interval z_iv[v in 1..V];

dvar interval z_oiv[v in 1..V][p in 1..P+1] optional;

dvar sequence task_sv[p in 1..P] in all (t in 1..T) task_oiv[t][p];

dvar int makespan;

// Cummulative functions

// number of loads and stores occuring in parallel
cumulFunction cfls = sum(t in 1..T) pulse(load_iv[t], 1) + sum(t in 1..T) pulse(store_iv[t], 1);

// total size of data objects loaded in each processor's scratchpad
cumulFunction cfvar[p in 1..P] = sum(v in 1..V) pulse(z_oiv[v][p], VarS[v]);

minimize makespan;
		 	
subject to {
	
	makespan == endOf(task_iv[T]);
	
	// each task must be scheduled to a processor
	forall(t in 1..T) alternative(task_iv[t], all(p in 1..P) task_oiv[t][p]);
  	    	
	// no overlap, for tasks at the same proc p
	forall(p in 1..P) noOverlap(task_sv[p]);
	
	// DAG constraints   	
    forall(e in 1..E) endBeforeStart(task_iv[Edges[e].node1], task_iv[Edges[e].node2]);  

	// load of variables for each task should start when the task starts 
	forall(t in 1..T) startAtStart(load_iv[t], task_iv[t]);

	// store of variables for each task should end when the task ends 
	forall(t in 1..T) endAtEnd(store_iv[t], task_iv[t]);

	// size of each load_iv
	forall(t in 1..T) {
		sizeOf(load_iv[t]) == sum(r in VarR: r.task_id == t) load_b[t][r.var_id] * r.gain;
	}

	// size of each store_iv
	forall(t in 1..T) {
		sizeOf(store_iv[t]) == sum(r in VarR: r.task_id == t) store_b[t][r.var_id] * r.gain;
	}

	// no more than 1 load or store operation at the same time (single communication channel constraint)
	cfls <= 1;

	// set lower limit for each task execution time 
	forall(t in 1..T) {
		sizeOf(task_iv[t]) >= sum(p in 1..P) presenceOf(task_oiv[t][p]) * 
							(Exec[t][p] - sum(r in VarR: r.task_id == t) presenceOf(z_oiv[r.var_id][p])  * r.gain * r.var_freq)
							+ sizeOf(load_iv[t]) + sizeOf(store_iv[t]);
	}

	// specify if task t1 loads variable v
	forall(t1 in 1..T, p in 1..P, t2 in 1..T, v in VarsThatTaskUses[t1]: 
			v in VarsThatTaskModify[t2] && t1 != t2 && t2 not in StartAfter[t1]) {
		presenceOf(z_oiv[v][p]) && presenceOf(task_oiv[t1][p]) && 
		sum(p1 in 1..P: p1 != p) presenceOf(task_oiv[t2][p1]) == 1 &&
		
		// t2 - t1
		startOf(task_oiv[t1][p]) >= endOf(task_iv[t2]) && 
		
		// no t2 - t3 - t1
		sum(t3 in 1..T: t3 != t1 && t3 != t2 && v in VarsThatTaskUses[t3] && t2 not in StartAfter[t3] && t3 not in StartAfter[t1]) 
			(presenceOf(task_oiv[t3][p]) &&
			 startOf(task_oiv[t3][p]) >= endOf(task_iv[t2]) && 
			 startOf(task_oiv[t1][p]) >= startOf(task_oiv[t3][p])) == 0
			
		=> load_b[t1][v] == 1;
	}

	// specify if task t1 stores variable v 
	forall(t1 in 1..T, p in 1..P, t2 in 1..T, v in VarsThatTaskModify[t1]:
			v in VarsThatTaskUses[t2] &&	t1 != t2 && t1 not in StartAfter[t2]) {
		presenceOf(z_oiv[v][p]) && presenceOf(task_oiv[t1][p]) && 
		sum(p1 in 1..P: p1 != p) presenceOf(task_oiv[t2][p1]) == 1 &&
		
		// t1 - t2
		startOf(task_iv[t2]) >= endOf(task_oiv[t1][p]) && 

		// no t1 - t3 - t2 
		sum(t3 in 1..T: t3 != t1 && t3 != t2 && v in VarsThatTaskModify[t3] && t1 not in StartAfter[t3] && t3 not in StartAfter[t2]) 
			(presenceOf(task_oiv[t3][p]) && 
			startOf(task_oiv[t3][p]) >= endOf(task_oiv[t1][p]) && 
			startOf(task_iv[t2]) >= endOf(task_oiv[t3][p])) == 0
			
		=> store_b[t1][v] == 1; 
	}

	// each data object must exist either in a scratchpad memory or in the main memory 
    forall(v in 1..V) alternative(z_iv[v], all(p in 1..P+1) z_oiv[v][p]);    	

	// scratchpad memory sizes should not be exceeded
	forall(p in 1..P) cfvar[p] <= SPMS[p];

	// specify start and end times of data objects in memories  		
	forall(v in 1..V) span(z_iv[v], all(t in TasksUsingVar[v]) task_iv[t]);
}

// execution
range Tasks = 1..T;
range Procs = 1..P;
range Vars = 1..V;

execute {
	cp.param.TimeLimit = 60;
	cp.param.LogPeriod = 100000;

	for(var t in Tasks){
		for (var p in Procs) {
			if (task_oiv[t][p].present)		
				writeln("Task" + t + " [" + task_iv[t].start + " - " + task_iv[t].end + "] scheduled at processor " + p);
		}			
	}
	
	for(var v in Vars) {
		if (z_oiv[v][P+1].present) {
			writeln("var: " + v + " is mapped to memory");
 		}			
		for (var p in Procs) {
			if (z_oiv[v][p].present) {
				writeln("var: " + v + " is mapped to proc: " + p + 
				 " start=" + z_oiv[v][p].start + " end=" + z_oiv[v][p].end + "[size=" + VarS[v] + "]");
   			}  				
  		}				
	}	
}
