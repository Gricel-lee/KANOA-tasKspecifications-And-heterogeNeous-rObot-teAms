
 // ----------------Initialize contraint solver-------------//
abstract sig Mission{
	dotask: one (AtomicTask + CompoundTask)
}
fact { all m:Mission | disj[m.dotask, (Mission-m).dotask] } // each mission belongs to different task


abstract sig AtomicTask {}

abstract sig CompoundTask{
	at: set AtomicTask,
    	ct: set CompoundTask
}
fact { all c:CompoundTask | disj[c.at, (CompoundTask-c).at] and disj[c.ct, (CompoundTask-c).ct] } // each compound task has its own tasks

fact{ all c:CompoundTask | #(ct.c)=1 or #(dotask.c)=1 } //compound task belong to another compound task or to a mission
fact{ all a:AtomicTask | #(at.a)=1 or #(dotask.a)=1 } //atomic task belong to another (compound) task or to a mission
fact{ all c:CompoundTask | #(c.at + c.ct)>1} //at+ct is not empty in a Compound task

 // ----------------Problem V2-------------//

 // ----------------ATOMIC TASKS:
    sig at4 extends AtomicTask{}{}
    sig at3 extends AtomicTask{}{}
    sig at6 extends AtomicTask{}{}
    sig at5 extends AtomicTask{}{}
    sig at8 extends AtomicTask{}{}
    sig at7 extends AtomicTask{}{}
    sig at9 extends AtomicTask{}{}
    sig at2 extends AtomicTask{}{}
    sig at1 extends AtomicTask{}{}
    sig at10 extends AtomicTask{}{}

 // ----------------COMPOUND TASKS:
    sig ct2 extends CompoundTask{}
        fact{all c:ct2  | #c.at = 1 and not disj[at4 , c.at]} //CT has 1 atomic tasks
        fact{all c:ct2  | #c.ct = 1 and not disj[ct1 , c.ct]} //CT has 1 compound tasks
    sig ct1 extends CompoundTask{}
        fact{all c:ct1  | #c.at = 2 and not disj[at1 , c.at] and not disj[at2 , c.at]} //CT has 2 atomic tasks
        fact{all c:ct1  | #c.ct = 0}
    sig ct4 extends CompoundTask{}
        fact{all c:ct4  | #c.at = 3 and not disj[at8 , c.at] and not disj[at9 , c.at] and not disj[at10 , c.at]} //CT has 3 atomic tasks
        fact{all c:ct4  | #c.ct = 0}
    sig ct3 extends CompoundTask{}
        fact{all c:ct3  | #c.at = 3 and not disj[at5 , c.at] and not disj[at6 , c.at] and not disj[at7 , c.at]} //CT has 3 atomic tasks
        fact{all c:ct3  | #c.ct = 0}
 // ----------------MISSION:
    sig t1 extends Mission{}
    {disj[dotask, (CompoundTask+AtomicTask - ct1) ] }
    sig t2 extends Mission{}
    {disj[dotask, (CompoundTask+AtomicTask - ct1) ] }
    sig t3 extends Mission{}
    {disj[dotask, (CompoundTask+AtomicTask - at3) ] }
    sig t4 extends Mission{}
    {disj[dotask, (CompoundTask+AtomicTask - ct2) ] }
    sig t5 extends Mission{}
    {disj[dotask, (CompoundTask+AtomicTask - ct3) ] }
    sig t6 extends Mission{}
    {disj[dotask, (CompoundTask+AtomicTask - ct4) ] }

 // ----------------RUN COMMAND:
pred TaskAllocation{
    #(t1)=1
    #(t2)=1
    #(t3)=1
    #(t4)=1
    #(t5)=1
    #(t6)=1
}
run TaskAllocation for exactly 6 Mission, 14 AtomicTask, 6 CompoundTask, exactly 1 at4, exactly 1 at3, exactly 1 at6, exactly 1 at5, exactly 1 at8, exactly 1 at7, exactly 1 at9, exactly 3 at2, exactly 3 at1, exactly 1 at10, exactly 1 ct2, exactly 3 ct1, exactly 1 ct4, exactly 1 ct3