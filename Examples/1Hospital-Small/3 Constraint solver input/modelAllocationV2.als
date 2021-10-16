
 // ----------------Initialize contraint solver-------------//
open util/integer

abstract sig Robot {
	hascapability : set Capability,
	totaltime : one Int,
	distX : one Int,
	distY : one Int,
	x : one Int,
	y : one Int
} 
abstract sig Capability {
    	belongsto: one Robot
}
fact { all c:Capability, r:Robot | r in c.belongsto <=> c in r.hascapability }

abstract sig AtomicTask {
    	runby: some Capability,
	time: Int,
	x : one Int,
	y : one Int
}

fact{ all r:Robot | !disj[r.hascapability, AtomicTask.runby] } //all robots that appear in the schema must be associated to a task


//----------- Functions

//function to get distance x cover by robot r -- instead of the area (XxY), as the number would get bigger (and hence the bidwitdh of "Int")  ---implemented as:	//mul [ minus [Xmax[r], Xmin[r] ] , 	minus [Ymax[r], Ymin[r]] ]
fun DistX [r: Robot] : Int { //in X  
	sub [Xmax[r] , Xmin [r] ]
}


//function to get distance y cover by robot r
fun DistY [r: Robot] : Int { //in Y 
	sub [Ymax[r] , Ymin [r] ]
}


fun Xmax [r: Robot] : Int {
	max [(runby.(r.hascapability)).x +  r.x] //max X of all tasks and robot itself
}

fun Xmin [r: Robot] : Int {
	min [(runby.(r.hascapability)).x +  r.x] //min X of all tasks and robot itself
}

fun Ymax [r: Robot] : Int {
	max [(runby.(r.hascapability)).y +  r.y] //max Y of all tasks and robot itself
}

fun Ymin [r: Robot] : Int {
	min [(runby.(r.hascapability)).y +  r.y] //min Y of all tasks and robot itself
}

// function returns the number of tasks i in robot r
fun numberTasksi[ati:AtomicTask , r:Robot] : Int {
	#( (runby.(r.hascapability) ) & ati )
}

 // ----------------Problem V2-------------//
 // ----------------ATOMIC TASKS:
    sig at4 extends AtomicTask{}
    {
        disj[runby, Capability - c3] and
        #runby=1 // 1 robot
        x = 75
        y = 125
        time = 4
    }
    sig at3 extends AtomicTask{}
    {
        disj[runby, Capability - c4] and
        #runby=2 // 2 robot
        all r:runby | disj[r,runby-r] //different robots
        x = 25
        y = 125
        time = 3
    }
    sig at6 extends AtomicTask{}
    {
        disj[runby, Capability - c6] and
        #runby=1 // 1 robot
        x = 75
        y = 125
        time = 1
    }
    sig at5 extends AtomicTask{}
    {
        disj[runby, Capability - c5] and
        #runby=1 // 1 robot
        x = 25
        y = 125
        time = 1
    }
    sig at8 extends AtomicTask{}
    {
        disj[runby, Capability - c8] and
        #runby=1 // 1 robot
        x = 25
        y = 125
        time = 1
    }
    sig at7 extends AtomicTask{}
    {
        disj[runby, Capability - c7] and
        #runby=1 // 1 robot
        x = 125
        y = 125
        time = 1
    }
    sig at9 extends AtomicTask{}
    {
        disj[runby, Capability - c9] and
        #runby=1 // 1 robot
        x = 75
        y = 125
        time = 1
    }
    sig at2 extends AtomicTask{}
    {
        disj[runby, Capability - c2] and
        #runby=1 // 1 robot
        x = 225
        y = 125
        time = 2
    }
    sig at1 extends AtomicTask{}
    {
        disj[runby, Capability - c1] and
        #runby=1 // 1 robot
        x = 25
        y = 125
        time = 1
    }
    sig at10 extends AtomicTask{}
    {
        disj[runby, Capability - c10] and
        #runby=1 // 1 robot
        x = 125
        y = 125
        time = 1
    }
 // ----------------CAPABILITIES:
    abstract sig c10 extends Capability{}
    abstract sig c1 extends Capability{}
    abstract sig c2 extends Capability{}
    abstract sig c3 extends Capability{}
    abstract sig c4 extends Capability{}
    abstract sig c5 extends Capability{}
    abstract sig c6 extends Capability{}
    abstract sig c7 extends Capability{}
    abstract sig c8 extends Capability{}
    abstract sig c9 extends Capability{}
    sig c10_instance0 ,c10_instance1  extends c10{}
    sig c1_instance0 ,c1_instance1  extends c1{}
    sig c2_instance0 ,c2_instance1  extends c2{}
    sig c3_instance0 ,c3_instance1  extends c3{}
    sig c4_instance0 ,c4_instance1  extends c4{}
    sig c5_instance0 ,c5_instance1  extends c5{}
    sig c6_instance0 ,c6_instance1  extends c6{}
    sig c7_instance0 ,c7_instance1  extends c7{}
    sig c8_instance0 ,c8_instance1  extends c8{}
    sig c9_instance0 ,c9_instance1  extends c9{}
 // ----------------ROBOTS:
    sig r2 extends Robot {}
    {
        #(hascapability & c1_instance0)=1 //has capabiityc1_instance0 
        #(hascapability & c2_instance0)=1 //has capabiityc2_instance0 
        #(hascapability & c3_instance0)=1 //has capabiityc3_instance0 
        disj[hascapability, Capability-(c1_instance0+c2_instance0+c3_instance0)] // no more capabilities
        x = 75
        y = 25
        distX = DistX[r2]
        distY = DistY[r2]
        totaltime = TotalTime[r2]
    }
    sig r3 extends Robot {}
    {
        #(hascapability & c10_instance0)=1 //has capabiityc10_instance0 
        #(hascapability & c4_instance0)=1 //has capabiityc4_instance0 
        #(hascapability & c5_instance0)=1 //has capabiityc5_instance0 
        #(hascapability & c6_instance0)=1 //has capabiityc6_instance0 
        #(hascapability & c7_instance0)=1 //has capabiityc7_instance0 
        #(hascapability & c8_instance0)=1 //has capabiityc8_instance0 
        #(hascapability & c9_instance0)=1 //has capabiityc9_instance0 
        disj[hascapability, Capability-(c10_instance0+c4_instance0+c5_instance0+c6_instance0+c7_instance0+c8_instance0+c9_instance0)] // no more capabilities
        x = 125
        y = 25
        distX = DistX[r3]
        distY = DistY[r3]
        totaltime = TotalTime[r3]
    }
    sig r4 extends Robot {}
    {
        #(hascapability & c10_instance1)=1 //has capabiityc10_instance1 
        #(hascapability & c4_instance1)=1 //has capabiityc4_instance1 
        #(hascapability & c5_instance1)=1 //has capabiityc5_instance1 
        #(hascapability & c6_instance1)=1 //has capabiityc6_instance1 
        #(hascapability & c7_instance1)=1 //has capabiityc7_instance1 
        #(hascapability & c8_instance1)=1 //has capabiityc8_instance1 
        #(hascapability & c9_instance1)=1 //has capabiityc9_instance1 
        disj[hascapability, Capability-(c10_instance1+c4_instance1+c5_instance1+c6_instance1+c7_instance1+c8_instance1+c9_instance1)] // no more capabilities
        x = 175
        y = 25
        distX = DistX[r4]
        distY = DistY[r4]
        totaltime = TotalTime[r4]
    }
    sig r1 extends Robot {}
    {
        #(hascapability & c1_instance1)=1 //has capabiityc1_instance1 
        #(hascapability & c2_instance1)=1 //has capabiityc2_instance1 
        #(hascapability & c3_instance1)=1 //has capabiityc3_instance1 
        disj[hascapability, Capability-(c1_instance1+c2_instance1+c3_instance1)] // no more capabilities
        x = 25
        y = 25
        distX = DistX[r1]
        distY = DistY[r1]
        totaltime = TotalTime[r1]
    }
// Function to add all atomic tasks times allocated to a robot
fun TotalTime [r: Robot] : Int { // 4 atomic tasks
		plus[ mul [ #( (runby.(r.hascapability) ) & at1 ) , at1.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at2 ) , at2.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at3 ) , at3.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at4 ) , at4.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at5 ) , at5.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at6 ) , at6.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at7 ) , at7.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at8 ) , at8.time] , 
		plus[ mul [ #( (runby.(r.hascapability) ) & at9 ) , at9.time] , 
		mul [ #( (runby.(r.hascapability) ) & at10 ) , at10.time] ]]]]]]]]]
}

 // ----------------PREDICATE:
pred TaskAllocation{
}

 // ----------------RUN COMMAND:
run TaskAllocation for 9 Int, 4 Robot, 1 r2, 1 r3, 1 r4, 1 r1, 20 Capability, 14 AtomicTask, exactly 1 at4, exactly 1 at3, exactly 1 at6, exactly 1 at5, exactly 1 at8, exactly 1 at7, exactly 1 at9, exactly 3 at2, exactly 3 at1, exactly 1 at10