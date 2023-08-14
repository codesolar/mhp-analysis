package submit_a3;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import dont_submit.MhpQuery;

import java.util.Set;
import java.util.Stack;

import javafx.util.Pair;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PatchingChain;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.UnitPatchingChain;
import soot.Value;
import soot.jimple.ClassConstant;
import soot.jimple.DefinitionStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.NopStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.spark.pag.AllocNode;
import soot.jimple.spark.pag.LocalVarNode;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.pag.PAG;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.graph.pdg.EnhancedUnitGraph;
import soot.util.Chain;
class CNode {
	String obj;
	Unit u;
	String cid;
	String sp;
	SootMethod me;
	CNode(String Object,Unit unit,String CallerID,String special,SootMethod method){
		this.obj = Object;
		this.u = unit;
		this.cid = CallerID;
		this.sp = special;
		this.me = method;
	}
	public boolean equals(Object o) {
		if(o instanceof CNode) {
			CNode t = (CNode)o;
			if(t.u == null && this.u != null) return false;
			if(t.u != null && this.u == null) return false;
			if((t.u == null && this.u == null) || (t.u.equals(this.u))){
				if(t.obj.equals(this.obj) && t.cid.equals(this.cid) && t.sp.equals(this.sp) && t.me.equals(this.me)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public int hashCode() {
		int hash;
		if(u == null)
			hash = 0;
		else 
			hash = u.hashCode();
		
		String str = "";
		str = str + hash + obj + cid + sp + me;
		return str.hashCode();
	}
	
}


class CEdge{
	CNode src;
	CNode dest;
	String type;
	CEdge(CNode source,CNode destination,String type){
		this.src = source;
		this.dest = destination;
		this.type = type;
	}
}


public class MhpAnalysis extends SceneTransformer{
	CallGraph cha;
//	Map<Integer,CNode> tnode;
//	CNode ttnode;
//	int unum = 0;
	Set<Unit> all;
	Map<CNode , Set<CEdge>> pegSuccs;
	Map<CNode , Set<CEdge>> pegPreds;
	PointsToSetInternal pts;
	Map<Node,String> objMap;
	Map<String, Node> revobjMap;
	int count;
	Set<String> possibleTypes;
	Map<Unit,Set<CNode>> cfg2pts;//just stores the header
	BriefUnitGraph cfg;
	Body arg0;
	Set<CNode> newly;
	CNode cn ;
	List<Unit> predUnitSet;
	List<Unit> succUnitSet;
	PAG pta;
	Chain<SootClass> classes;
	Set<SootClass> classSet;
	Set<SootMethod> setOfMethods;
	CEdge tempCEdge;
	Stmt stmt;
	String obj = null;
	String cid = null;
	String special = null;
	Set<CNode> succ;
	CNode pred;
	Set<CNode> processed;
	CNode root;
	Map<String,Set<CNode>> notifymap;
	Map<String,Set<CNode>> monitormap;
	Map<String,Integer> lockcount; 
	Set<CNode> monitorset;
	Set<CNode> vis;
	Map<CNode,Set<CNode>> KILL;
	Map<CNode,Set<CNode>> GEN;
	Map<CNode,Set<CNode>> M;
	Map<CNode,Set<CNode>> OUT;
	Map<String,Set<CNode>> N;
	Set<CNode> worklist;
	Map<CNode,Set<CNode>> notifysucc;
	Map<CNode,CNode> cnlockmap;;
	void cfg2ptsinsert(Unit u , CNode cn) {
		if(!cfg2pts.containsKey(u)) {
			Set<CNode> tempSet = new HashSet<>();
			cfg2pts.put(u, tempSet);
		}
		Set<CNode> set = cfg2pts.get(u);
		boolean found = false;
		for(CNode c:set) {
			if(c.equals(cn)) {
				found = true;
				break;
			}
		}
		
		if(found == false) {
			set.add(cn);
			cfg2pts.put(u, set);
		}
	}
	boolean inpro(CNode cn) {
		for(CNode c:processed) {
			if(cn.equals(c)) return true;
		}
		return false;
	}
//	void printMap(Map<CNode , Set<CEdge>> pegmap) {
////		System.out.println("THE PEGMAP IS = ");
//		for(Map.Entry<CNode, Set<CEdge>> entry:pegmap.entrySet()) {
////			System.out.println("VERTEX IS = ");
////			printvertex(entry.getKey());
//			
//			for(CEdge ce:entry.getValue()) {
////				printedge(ce);
//			}
////			System.out.println("::::::::::::::::::::::::::::::::::");
//		}
//	}
//	void printvertex(CNode cn) {
//		System.out.println(cn.obj + "  "+ cn.u + "  " + cn.cid + "  " + cn.sp + "  " + cn.me.getName());
//	}
//	
//	void printedge(CEdge ce) {
//		System.out.print("DEST IS = ");
//		printvertex(ce.dest);
//		System.out.println(ce.type);
//	}
	
	
	void addedge(CNode c1,CNode c2,String str1,String str2) {
		Set<CEdge> setCEdge;
		if(c1 == null || c2 == null) return;
		if(!pegSuccs.containsKey(c1)) {
			setCEdge = new HashSet<>();
			pegSuccs.put(c1,setCEdge);
		}
		if(!pegPreds.containsKey(c2)) {
			setCEdge = new HashSet<>();
			pegPreds.put(c2,setCEdge);
		}
		
		tempCEdge = new CEdge(c1,c2,str1);
		setCEdge = pegSuccs.get(c1);
		boolean found = false;
		for(CEdge ce:setCEdge) {
			if(ce.dest.equals(c2) && ce.type.equals(str1)){//if something happens look here in the ce.dest.equals as null can be there
				found = true;
				break;
			}
		}
		if(found == false) {
			setCEdge.add(tempCEdge);
			pegSuccs.put(c1, setCEdge);
		}
		
		
		
		
		found = false;

		
		
		tempCEdge = new CEdge(c2,c1,str2);
		setCEdge = pegPreds.get(c2);
		for(CEdge ce:setCEdge) {
			if(ce.dest.equals(c1) && ce.type.equals(str2)){//if something happens look here in the ce.dest.equals as null can be there
				
				found = true;
				break;
			}
		}
		
		if(found == false) {
			setCEdge.add(tempCEdge);
			pegPreds.put(c2, setCEdge);
		}

	}
	
	Set<CNode> startpred(CNode n){
		Set<CNode> res = new HashSet<>();
		if(!pegPreds.containsKey(n)) return res;
		Set<CEdge> set = pegPreds.get(n);
		for(CEdge ce:set) {
			if(ce.type.equals("startpred")) {
				res.add(ce.dest);
			}
		}
		
		return res;
	}
	
	Set<CNode> startsucc(CNode n){
		Set<CNode> res = new HashSet<>();
		if(!pegSuccs.containsKey(n)) return res;
		Set<CEdge> set = pegSuccs.get(n);
		for(CEdge ce:set) {
			if(ce.type.equals("startsucc")) {
				res.add(ce.dest);
			}
		}
		
		return res;
	}
	

	
	Set<CNode> waitingsucc(CNode n){
		Set<CNode> res = new HashSet<>();
		if(!pegSuccs.containsKey(n)) return res;
		Set<CEdge> set = pegSuccs.get(n);
		for(CEdge ce:set) {
			if(ce.type.equals("waitingsucc")) {
				res.add(ce.dest);
			}
		}
		
		return res;
	}
	
	
	Set<CNode> waitingpred(CNode n){
		Set<CNode> res = new HashSet<>();
		if(!pegPreds.containsKey(n)) return res;
		Set<CEdge> set = pegPreds.get(n);
		for(CEdge ce:set) {
			if(ce.type.equals("waitingpred")) {
				res.add(ce.dest);
			}
		}
		
		return res;
	}
	
	
	Set<CNode> waitingnode(String obj){
		Set<CNode> set = getallnodes();
		Set<CNode> res = new HashSet<>();
		for(CNode cn:set) {
			if(cn.sp.equals("waiting") && (cn.obj.equals(obj))) {
				res.add(cn);
			}
		}
		return res;
	}

	Set<CNode> notifypred(CNode n){
		Set<CNode> res = new HashSet<>();
		if(!pegPreds.containsKey(n)) return res;
		Set<CEdge> set = pegPreds.get(n);
		for(CEdge ce:set) {
			if(ce.type.equals("notifypred")) {
				res.add(ce.dest);
			}
		}
		
		return res;
	}
	
	Set<CNode> localpred(CNode n){
		Set<CNode> res = new HashSet<>();
		if(!pegPreds.containsKey(n)) return res;
		Set<CEdge> set = pegPreds.get(n);
		for(CEdge ce:set) {
			if(ce.type.equals("normalpred")) {
				res.add(ce.dest);
			}
		}
		
		return res;
	}
	
	
	Set<CNode> localsucc(CNode n){
		Set<CNode> res = new HashSet<>();
		if(!pegSuccs.containsKey(n)) return res;
		Set<CEdge> set = pegSuccs.get(n);
		for(CEdge ce:set) {
			if(ce.type.equals("normal")) {
				res.add(ce.dest);
			}
		}
		
		return res;
	}
	CNode changer(CNode cn) {
		Unit exitu = enterexit.get(cn.u);
		CNode ne = new CNode(cn.obj,exitu,cn.cid,"exit",cn.me);
		return ne;
	}
	CNode revchanger(CNode cn) {
		Unit entryu = enterexit.get(cn.u);
		if(exitenter.containsKey(cn.u)) {
//			System.out.println("LLLLLLLL");
		}
//		System.out.println(cn.u);
//		System.out.println("LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLL");
		for(Map.Entry<Unit, Unit> entry:enterexit.entrySet()) {
//			System.out.println(entry.getKey());
//			System.out.println(entry.getValue());
		}
//		System.out.println(entryu);
		CNode ne = new CNode(cn.obj,entryu,cn.cid,"entry",cn.me);
		return ne;
	}
	void monitormapupdater(Set<CNode> monitorset) {//working but problrm when nested structure is there
//		System.out.println("hello");
		for(CNode cn : monitorset) {
//			printvertex(cn);
			Set<CNode> set1 = new HashSet<>();
			String lockobj = cn.obj;
			if(monitormap.containsKey(lockobj)) {
				set1 = monitormap.get(lockobj);
			}
			if(!set1.contains(cn)) {
				Set<CNode> set2 = reach(cn);
				set1.addAll(set2);
				monitormap.put(lockobj, set1);
			}	
		}
		
		for(Map.Entry<String, Set<CNode>> entry:monitormap.entrySet()) {
			Set<CNode> set1 = entry.getValue();
			Set<CNode> set2 = new HashSet<>();
			set2.addAll(set1);
			for(CNode cn:set1) {
				if(cn.sp.equals("waiting")) {
					set2.remove(cn);
				}
				else if(cn.sp.equals("notified_entry")) {
					set2.remove(cn);
				}
			}
			set1 = set2;
			monitormap.put(entry.getKey(), set1);
		}
	}
	Set<CNode> reach(CNode cn){
//		System.out.println(":::::::::::::::::___________");
//		printvertex(cn);
		String lock = cn.obj;
		Unit obj = cn.u;
		CNode exit = changer(cn);
		Map<Pair<String,String>,Integer> lom = new HashMap<>();
		Set<CNode> queue = new HashSet<>();
		Set<CNode> proc = new HashSet<>();
		Pair<String,String> p1 = new Pair<String,String>(cn.obj,cn.cid);
		if(!lom.containsKey(p1)) {
			lom.put(p1, 1);
		}

		for(CEdge c : pegSuccs.get(cn)) {
			if(c.type.equals("normal") && c.dest.cid.equals(cn.cid)) {
				queue.add(c.dest);
			}
		}
		
		while(queue.size() != 0) {
			int num = queue.size();
			for(int i = 0;i < num;i ++) {
				CNode rem = queue.iterator().next();
				queue.remove(rem);
				proc.add(rem);
//				System.out.println("START");
//				printvertex(rem);
				int c = 0;
				if(rem.sp.equals("exit")) {
					p1 = new Pair<>(rem.obj,rem.cid);
					if(!lom.containsKey(p1)) {
						lom.put(p1, 0);
					}
					c = lom.get(p1);
					c = c - 1;
					lom.put(p1, c);
				}
				else if(rem.sp.equals("entry")) {
					p1 = new Pair<>(rem.obj,rem.cid);
					if(!lom.containsKey(p1)) {
						lom.put(p1, 0);
					}
					c = lom.get(p1);
					c = c + 1;
					lom.put(p1, c);
				}
				
//				System.out.println("KK");
				if(!rem.equals(exit)) {
					if(rem.sp.equals("exit") && c < 0) {
						
					}
					else {
						for(CEdge cv:pegSuccs.get(rem)) {
							if(!proc.contains(cv.dest)&& cv.dest.cid.equals(cn.cid)) {
								queue.add(cv.dest);
							}	
						}	
					}
					
				}
				
			}
			
			
		}
		return proc;
	}

	Set<CNode> getallnodes(){
		Set<CNode> set = new HashSet<>();
		for(Map.Entry<CNode, Set<CEdge>> entry:pegSuccs.entrySet()) {
			set.add(entry.getKey());
		}
		
		for(Map.Entry<CNode, Set<CEdge>> entry:pegPreds.entrySet()) {
			set.add(entry.getKey());
		}
		
		return set;
	}
	
	void margin() {
		Set<CNode> set = getallnodes();
		for(CNode cn : set) {
			if(!pegSuccs.containsKey(cn)) {
				Set<CEdge> cset = new HashSet<>();
				pegSuccs.put(cn, cset);
			}
			if(!pegPreds.containsKey(cn)) {
				Set<CEdge> cset = new HashSet<>();
				pegPreds.put(cn, cset);
			}
		}
	}
	void computeN(){
		N = new HashMap<>();
		for(Map.Entry<CNode, Set<CEdge>> entry:pegSuccs.entrySet()) {
			if(!N.containsKey(entry.getKey().cid)) {
				Set<CNode> set = new HashSet<>();
				N.put(entry.getKey().cid, set);
			}
			Set<CNode> set = N.get(entry.getKey().cid);
			set.add(entry.getKey());
			N.put(entry.getKey().cid, set);	
		}
	}
	
	
	Set<CNode> reachablestart(String t){
		
		Set<CNode> vis = new HashSet<>();
		CNode nd = root;
		Set<CNode> queue = new HashSet<>();
		Set<CNode> res = new HashSet<>();
		queue.add(nd);
		vis.add(nd);

		while(queue.size() != 0) {
			nd = queue.iterator().next();
			queue.remove(nd);
			for(CEdge ce:pegSuccs.get(nd)) {
				if(!vis.contains(ce.dest)) {
					vis.add(ce.dest);
					queue.add(ce.dest);
					if(ce.dest.sp.equals("start")) {
						res.add(ce.dest);
					}
				}
			}
		}
		
		return res;
	}
	
	void initialize() {
		Set<CNode> set = getallnodes();
		notifysucc = new HashMap<>();
		KILL = new HashMap<>();
		GEN = new HashMap<>();
		M = new HashMap<>();
		OUT = new HashMap<>();
		
		for(CNode cn :set) {
			Set<CNode> set1 = new HashSet<>();
			KILL.put(cn, set1);
			set1 = new HashSet<>();
			GEN.put(cn, set1);
			set1 = new HashSet<>();
			M.put(cn, set1);
			set1 = new HashSet<>();
			OUT.put(cn, set1);
			set1 = new HashSet<>();
			notifysucc.put(cn,  set1);
		}
		
		worklist = new HashSet<>();
		worklist.addAll(reachablestart("main"));
		
		
		
	}
	Set<CNode> gennotifyall(CNode n) {
		Set<CNode> res = new HashSet<>();
		Set<CNode> set = getallnodes();
		if(n.sp.equals("notified_entry")) {
			for(CNode m:set) {
				if(!m.equals(n) && m.obj.equals(n.obj) && m.sp.equals("notified_entry")) {
					CNode wpn = waitingpred(n).iterator().next();
					CNode wpm = waitingpred(m).iterator().next();
					if(M.get(wpm).contains(wpn)) {
						Set<CNode> mhpn = M.get(wpn);
						Set<CNode> mhpm = M.get(wpm);
						Set<CNode> dummy = new HashSet<>();
						dummy.addAll(mhpn);
						dummy.retainAll(mhpm); //mhpn now stores their intersection
						for(CNode r:set) {
							if(r.obj.equals(n.obj) && r.sp.equals("notifyAll") && dummy.contains(r)) {
								res.add(m);
							}
						}
					}
				}
			}
		}
		
		return res;
		
	}
	
	void firststage() {
		Set<CNode> set = getallnodes();
		for(CNode n:set) {
			
			
			if(n.sp.equals("join")) {
				Stmt stmt = (Stmt)n.u;
				InstanceInvokeExpr expr = (InstanceInvokeExpr)stmt.getInvokeExpr();
				if(expr instanceof VirtualInvokeExpr) {
//					System.out.println("virtual invoke STMT");
					Local base = (Local)expr.getBase();
					SootMethod meth = expr.getMethod();
		
					pts = (PointsToSetInternal) pta.reachingObjects(base);
					Set<String> ptsSet = new HashSet<>();
					P2SetVisitor vis = new P2SetVisitor() {

			               @Override
			               public void visit(Node n) {
			            	   ptsSet.add(objMap.get(n));
			               }

			        };
			        (pts).forall(vis); 
			        if(ptsSet.size() == 1) {
			        	Set<CNode> set1 = KILL.get(n);
						set1.addAll(N.get(n.obj));
						KILL.put(n, set1);
					}
				}	
			}
			else if(n.sp.equals("entry")) {
				Value v = ((EnterMonitorStmt) n.u).getOp();
				pts = (PointsToSetInternal) pta.reachingObjects((Local) v);
				Set<String> ptsSet = new HashSet<>();
				P2SetVisitor vis = new P2SetVisitor() {

		               @Override
		               public void visit(Node n) {
		            	   ptsSet.add(objMap.get(n));
		               }

		        };
		        (pts).forall(vis); //pti is the *PointsToSetInternal* set
		        
		        
		        if(ptsSet.size() == 1) {
		        	Set<CNode> set1 = KILL.get(n);
					if(monitormap.containsKey(n.obj)) {
						set1.addAll(monitormap.get(n.obj));
					}		
					KILL.put(n, set1);
		        }	
			}
			else if(n.sp.equals("notified_entry")) {
				Stmt stmt = (Stmt)n.u;
				InstanceInvokeExpr expr = (InstanceInvokeExpr)stmt.getInvokeExpr();
				if(expr instanceof VirtualInvokeExpr) {
//					System.out.println("virtual invoke STMT");
					Local base = (Local)expr.getBase();
					SootMethod meth = expr.getMethod();
		
					pts = (PointsToSetInternal) pta.reachingObjects(base);
					Set<String> ptsSet = new HashSet<>();
					P2SetVisitor vis = new P2SetVisitor() {

			               @Override
			               public void visit(Node n) {
			            	   ptsSet.add(objMap.get(n));
			               }

			        };
			        (pts).forall(vis); 
			        if(ptsSet.size() == 1) {
			        	Set<CNode> set1 = KILL.get(n);
						if(monitormap.containsKey(n.obj)) {
							set1.addAll(monitormap.get(n.obj));
						}
						KILL.put(n, set1);
					}
				}	
			}
			else if(n.sp.equals("notifyAll")) {
				Stmt stmt = (Stmt)n.u;
				InstanceInvokeExpr expr = (InstanceInvokeExpr)stmt.getInvokeExpr();
				if(expr instanceof VirtualInvokeExpr) {
//					System.out.println("virtual invoke STMT");
					Local base = (Local)expr.getBase();
					SootMethod meth = expr.getMethod();
		
					pts = (PointsToSetInternal) pta.reachingObjects(base);
					Set<String> ptsSet = new HashSet<>();
					P2SetVisitor vis = new P2SetVisitor() {

			               @Override
			               public void visit(Node n) {
			            	   ptsSet.add(objMap.get(n));
			               }

			        };
			        (pts).forall(vis); 
			        if(ptsSet.size() == 1) {
			        	Set<CNode> set1 = KILL.get(n);
						set1.addAll(waitingnode(n.obj));
						KILL.put(n, set1);
					}
				}	
				
			}
			else if(n.sp.equals("notify")) {
				Stmt stmt = (Stmt)n.u;
				InstanceInvokeExpr expr = (InstanceInvokeExpr)stmt.getInvokeExpr();
				if(expr instanceof VirtualInvokeExpr) {
//					System.out.println("virtual invoke STMT");
					Local base = (Local)expr.getBase();
					SootMethod meth = expr.getMethod();
		
					pts = (PointsToSetInternal) pta.reachingObjects(base);
					Set<String> ptsSet = new HashSet<>();
					P2SetVisitor vis = new P2SetVisitor() {

			               @Override
			               public void visit(Node n) {
			            	   ptsSet.add(objMap.get(n));
			               }

			        };
			        (pts).forall(vis); 
			        if(ptsSet.size() == 1) {
			        	Set<CNode> set1 = KILL.get(n);
			        	if(waitingnode(n.obj).size() == 1) {
							set1.addAll(waitingnode(n.obj));
						}
			        	KILL.put(n, set1);//start her
					}
				}	
				
			}
			
			else if(n.sp.equals("start")) {
				Set<CNode> set1 = GEN.get(n);
				Iterator<Edge> it = cha.edgesOutOf(n.u);
				while(it.hasNext()) {
					Edge e = it.next();
					SootMethod tgtMethod = (SootMethod) e.getTgt();
					if(setOfMethods.contains(tgtMethod)) {
						CNode begincn = new CNode("*",null,n.obj,"begin",tgtMethod);
						if(!GEN.containsKey(n)) {
							Set<CNode> set2 = new HashSet<>();
							GEN.put(n, set2);
						}
						Set<CNode> set2 = new HashSet<>();
						set2.add(begincn);
						GEN.put(n, set2);
					}
				}
			}
		}
	}
	
	
	void secondstage() {
		Set<CNode> allnodes = getallnodes();
		while(worklist.size() != 0) {
//			System.out.println("I");
			CNode n = worklist.iterator().next();
			worklist.remove(n);
			
			
			Set<CNode> M_old = new HashSet<>();
			Set<CNode> OUT_old = new HashSet<>();
			Set<CNode> notifysucc_old = new HashSet<>();
			
			Set<CNode> M_new = M.get(n);
			Set<CNode> OUT_new = OUT.get(n);
			Set<CNode> notifysucc_new = notifysucc.get(n);
			
			
			for(CNode cn : M_new) {
				M_old.add(cn);
			}
			
			for(CNode cn : OUT_old) {
				OUT_old.add(cn);
			}
			
			for(CNode cn : notifysucc_old) {
				notifysucc_old.add(cn);
			}
			
			
			
			
			Set<CNode> gennotifyallset = gennotifyall(n);

			
			Set<CNode> dummy = new HashSet<>();
			if(n.sp.equals("begin")) {
				Set<CNode> startpredset = startpred(n);
				for(CNode p:startpredset) {
					dummy.addAll(OUT.get(p));
				}
				
				dummy.removeAll(N.get(n.cid));
			}
			else if(n.sp.equals("notified_entry")) {
				Set<CNode> notifypredset = notifypred(n);
				for(CNode p : notifypredset) {
					dummy.addAll(OUT.get(p));
				}
				Set<CNode> outofwaitingpredset = OUT.get(waitingpred(n).iterator().next());
				dummy.retainAll(outofwaitingpredset);
				dummy.addAll(gennotifyallset);
				
			}
			else {
				Set<CNode> localpredset = localpred(n);
				for(CNode p:localpredset) {
					dummy.addAll(OUT.get(p));
				}
			}
			
//			System.out.println("K");
			M_new.addAll(dummy);
			
			M.put(n, M_new);
			
			
//			if(GEN.get(n) == null) System.out.println("P");
			
			if(notifymap.containsKey(n.obj)) {
//				System.out.println("P");
				Set<CNode> waitingset = waitingnode(n.obj);
				for(CNode m:waitingset) {
					if(M.get(n).contains(m)) {
						Set<CNode> waitingsuccset = waitingsucc(m);
						for(CNode m1:waitingsuccset) {
							addedge(n,m1,"notifysucc","notifypred");
							notifysucc_new.add(m1);
						}
					}
				}
//				System.out.println("P");
				for(CNode newn:notifysucc_new) {
					if(!notifysucc_old.contains(newn)) {
//						System.out.println("P");
						worklist.addAll(notifysucc_new);
						notifysucc.put(n, notifysucc_new);
						break;
					}
				}
//				System.out.println("P");
			}
			
			
//			if(GEN.get(n) == null) System.out.println("P");
			
			if(notifymap.containsKey(n.obj)) {
				Set<CNode> genn = new HashSet<>();
				if(notifysucc.containsKey(n)) {
					genn = notifysucc.get(n);
					GEN.put(n, genn);
				}
			}
//			if(GEN.get(n) == null) System.out.println("P");
//			if(n.sp.equals("exit")) {
//				CNode entrycn = revchanger(n);
//				Set<CNode> killset = new HashSet<>();
//				if(entrycn != null) {
////					printvertex(entrycn);
//					killset = KILL.get(entrycn);
//				}
//				 
//				GEN.put(n, killset);
//			}
//			if(GEN.get(n) == null) System.out.println("P");
			Set<CNode> msetofn = M_new;
			Set<CNode> gensetofn = GEN.get(n);
			Set<CNode> killsetofn = KILL.get(n);

			
			OUT_new.addAll(msetofn);
//			if(gensetofn == null) System.out.println("P");
			if(GEN.get(n) == null) System.out.println("P");
			OUT_new.addAll(gensetofn);
			
//			System.out.println("P");
//			System.out.println("T");
			OUT_new.removeAll(killsetofn);
			OUT.put(n, OUT_new);
			
			
//			System.out.println("T");
			dummy = new HashSet<>();
			dummy.addAll(M.get(n));
			dummy.removeAll(M_old);
			for(CNode m:dummy) {
				Set<CNode> set1 = M.get(m);
				set1.add(n);
				M.put(m,set1);
				worklist.add(m);
			}
			
//			System.out.println("J");
			
			
			OUT_new = OUT.get(n);
			if(!OUT_new.equals(OUT_old)) {
				worklist.addAll(localsucc(n));
				worklist.addAll(startsucc(n));
			}
		}
	}
	
	
	
	
	void analyze() {
		initialize();
		computeN();
		firststage();
		secondstage();
	}
	
	Set<Unit> dfsvis;
	Map<Unit,Unit> exitenter;
	Map<Unit,Unit> enterexit;
	Stack<Unit> stacklock;
	void dfs(BriefUnitGraph cfg ,Unit u) {
		List<Unit> succlist = cfg.getSuccsOf(u);
		for(Unit succ:succlist) {
			if(!dfsvis.contains(succ)) {
				Stmt succstmt = (Stmt)succ;
				if(succstmt instanceof EnterMonitorStmt) {
					stacklock.push(succ);
				}
				else if(succstmt instanceof ExitMonitorStmt) {
					if(stacklock.size() != 0) {
						Unit h = stacklock.peek();
						stacklock.pop();
						exitenter.put(succ, h);
					}
				}
				dfsvis.add(succ);
				dfs(cfg,succ);
			}
		}
	}
	void dfshelper(SootMethod m) {
		stacklock = new Stack<>();
		Body arg = m.getActiveBody();
		BriefUnitGraph cfg = new BriefUnitGraph(arg);
		List<Unit> list = cfg.getHeads();
		for(Unit u:list) {
			if(!dfsvis.contains(u)) {
				dfsvis.add(u);
				dfs(cfg,u);
			}
		}
	}
	protected void internalTransform(String phaseName, Map<String, String> options) {
		all = new HashSet<>();
		cha = Scene.v().getCallGraph();
		objMap = new HashMap<>();
		revobjMap = new HashMap<>();
		count = 0;
		pegSuccs = new HashMap<>();
		pegPreds = new HashMap<>();
		pta = (PAG) Scene.v().getPointsToAnalysis();
		classes = Scene.v().getApplicationClasses();
		classSet = new HashSet<>();
		setOfMethods = new HashSet<>();
		possibleTypes = new HashSet<>();
		cfg2pts = new HashMap<>();
		Set<CNode> queue = new HashSet<>();
		succ = new HashSet<>();
		pred = null;
		processed = new HashSet<>();
//		waitingmap = new HashMap<>();
		notifymap = new HashMap<>();
		monitorset = new HashSet<>();
		monitormap = new HashMap<>();
		vis = new HashSet<>();
		cnlockmap = new HashMap<>();
		enterexit = new HashMap<>();
		exitenter = new HashMap<>();
		dfsvis = new HashSet<>();
		
//		------------------------------------------possible types ---------------------------------------
		for(SootClass cls : classes) {
			if(!cls.getName().startsWith("jdk")) {
				classSet.add(cls);
		    	List<SootMethod> list = cls.getMethods();
		    	Iterator<SootMethod> methodIterator = list.iterator();
		    	possibleTypes.add(cls.toString());
			}
		}
//		-------------------------------------------------------------------------------------------------

		
		
//		---------------------------------set of methods and objMap and revobjMap created ----------------
		for (SootClass cls : classes) {
		    if(!cls.getName().startsWith("jdk")) {
		    	classSet.add(cls);
		    	List<SootMethod> list = cls.getMethods();
		    	Iterator<SootMethod> methodIterator = list.iterator();
		    	while(methodIterator.hasNext()) {
//		    		System.out.println("---------------------------");
		    		SootMethod met = methodIterator.next();
		    		if(!met.getName().equals("<init>")) {
		    			setOfMethods.add(met);
		    			
		    			Body arg0 = met.getActiveBody();
		    		    
//			    		System.out.println(met.toString());
//			    		System.out.println(met.getName());
//			    		System.out.println(arg0);
			    		Chain<Local> chain = arg0.getLocals();
			    		for(Local l : chain) {
//			    			System.out.println("Local is = " + l);
			    			pts = (PointsToSetInternal) pta.reachingObjects(l);
			    			P2SetVisitor vis = new P2SetVisitor() {

				                @Override
				                public void visit(Node n) {
				                	
				                	
				                	if(!objMap.containsKey(n) && possibleTypes.contains(n.getType().toString())) {
				                		obj = "R" + count;
					                	count ++;
					                	objMap.put(n ,  obj);
					                	revobjMap.put(obj, n);
//					                	System.out.println("TYPE IS = "  + n.getType());
//					                	System.out.println("object created = " + obj + "and node is = "+  n);
				                	}
				                	
				        
//				             	   System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>" + n +"<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
//				             	   System.out.println(n.getNumber());
//				             	   System.out.println(n.getType());
				                }

				             };
				              (pts).forall(vis); //pti is the *PointsToSetInternal* set
			    		}
		    		}
		    		
		    	}
		    }
		}
//		System.out.println("-------------------------objMap printing-----------------------------");
		for(Map.Entry<Node,String> entry:objMap.entrySet()) {
//			System.out.println(entry.getKey());
//			System.out.println(entry.getValue());
//			System.out.println(entry.getKey().getNumber());
//			System.out.println(entry.getKey().getType());
//			System.out.println(((AllocNode) entry.getKey()).getMethod());
		}
		
//		System.out.println("-------------------------revobjMap printing-----------------------------");
		for(Map.Entry<String,Node> entry:revobjMap.entrySet()) {
//			System.out.println(entry.getKey());
//			System.out.println(entry.getValue());
		}
		
//		------------------------------------------------------------------------------------------------------
		for(SootMethod sm:setOfMethods) {
//			System.out.println(sm.getName());
		}
		SootMethod mainMethod = null;
		for(SootMethod met1:setOfMethods) {
			if(met1.getName().equals("main")) {
				mainMethod = met1;
				break;
			}
		}
		
//		System.out.println("_________________________________________");
		for(SootMethod sm:setOfMethods) {
			dfshelper(sm);
		}
		
		
		
		for(Map.Entry<Unit, Unit> entry:exitenter.entrySet()) {
			enterexit.put(entry.getValue(), entry.getKey());
		}
//		System.out.println("_________________________________________");
		root = new CNode("*",null,"main","begin",mainMethod);
				
				
		Pair<SootClass,SootMethod> main = new Pair<SootClass,SootMethod>(mainMethod.getDeclaringClass(),mainMethod);
		arg0 = main.getValue().getActiveBody();
		cfg = new BriefUnitGraph(arg0);
		List<Unit> headL =  cfg.getHeads();
		for(Unit head : headL) {
			Stmt headstmt = (Stmt)head;
			CNode headcn = null;
			if(headstmt instanceof DefinitionStmt) {
				headcn = new CNode("*",head,"main","definition",main.getValue());
				queue.add(headcn);
				cfg2ptsinsert(head,headcn);
			}
			else if(headstmt instanceof NopStmt){
				headcn = new CNode("*",head,"main","nop",main.getValue());
				queue.add(headcn);
				cfg2ptsinsert(head,headcn);
			}
			
			else if(headstmt instanceof GotoStmt){
				headcn = new CNode("*",head,"main","goto",main.getValue());
				queue.add(headcn);
				cfg2ptsinsert(head,headcn);
			}
			
			addedge(root,headcn,"normal","normalpred");
		}
//		System.out.println("KKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK");
		
		

		while(queue.size() != 0) {
//			System.out.println("START OF WHILE QUEUE = ");
			for(CNode q:queue) {
//				printvertex(q);
			}
			
//			System.out.println("AFTER QUEUE PRINTING DONE");
			CNode curr = queue.iterator().next();
			queue.remove(curr);
			
			
//			System.out.println("BEFORE PROCESSED PRINTING DONE");
//			for(CNode q:processed) {
//				printvertex(q);
//			}
//			System.out.println("AFTER PROCESSED PRINTING DONE");
			
//			System.out.println("THE VERTEX GOING TO BE PROCESSED = ");
//			printvertex(curr);
//			System.out.println("CURRENT METHOD BODY IS = ");
//			System.out.println(curr.me.getActiveBody());
			cfg = new BriefUnitGraph(curr.me.getActiveBody());
			
			Stmt currstmt = (Stmt)curr.u;
			pred = curr;
			succ = new HashSet<>();
//			System.out.println("SUCCESSOR OF THIS IS = ");
//			System.out.println(cfg.getSuccsOf(curr.u));
			if(currstmt.containsInvokeExpr()) {
				InstanceInvokeExpr currexpr = (InstanceInvokeExpr)currstmt.getInvokeExpr();
				Local lbase = (Local)currexpr.getBase();
//				System.out.println("BASE = " + lbase);
//				System.out.println("THE FOLLOWING ARE THE OBJECTS OF THIS LOCAL = ");
			
				if(currexpr instanceof VirtualInvokeExpr) {
					Iterator<Edge> it = cha.edgesOutOf(curr.u);
					while(it.hasNext()) {
						Edge e = it.next();
						SootMethod src = (SootMethod)e.getSrc();
						SootMethod tgtMethod = (SootMethod) e.getTgt();
						SootClass tgtClass = tgtMethod.getDeclaringClass();
//						System.out.print(tgtMethod.getName());
						if(tgtMethod.getName().equals("run")) {
//							System.out.println("OUTER RUN");
							Body tgtbody = tgtMethod.getActiveBody();
							BriefUnitGraph tgtcfg = new BriefUnitGraph(tgtbody);
							List<Unit> tgthead =  tgtcfg.getHeads();
							CNode begincn = new CNode("*",null,curr.obj,"begin",tgtMethod);
							
							for(Unit tgtunit:tgthead) {
								Stmt tgtstmt = (Stmt)tgtunit;
								CNode headcn = null;
								if(tgtstmt instanceof DefinitionStmt) {
									headcn = new CNode("*",tgtunit,curr.obj,"definition",tgtMethod);
									queue.add(headcn);
									cfg2ptsinsert(tgtunit,headcn);
								}
								else if(tgtstmt instanceof NopStmt){
									headcn = new CNode("*",tgtunit,curr.obj,"nop",tgtMethod);
									queue.add(headcn);
									cfg2ptsinsert(tgtunit,headcn);
								}
								
								else if(tgtstmt instanceof GotoStmt){
									headcn = new CNode("*",tgtunit,curr.obj,"goto",tgtMethod);
									queue.add(headcn);
									cfg2ptsinsert(tgtunit,headcn);
								}
								
								//
								
								addedge(begincn,headcn,"normal","normalpred");
								if(!inpro(headcn))
									queue.add(headcn);
								
							}
							
							
							addedge(curr,begincn,"startsucc","startpred");							
							
							
							
						}//run ends
						
						
						else if(tgtMethod.getName().equals("wait")) {
//							System.out.println("OUTER WAIT");
							CNode waitingcn = new CNode(curr.obj,curr.u,curr.cid,"waiting",curr.me);

							cfg2ptsinsert(curr.u,waitingcn);
							
							
							
							addedge(curr,waitingcn,"normal","normalpred");
							//adding in waitingset
//							Set<CNode> waitingset = null;
//							if(!waitingmap.containsKey(curr.obj)) {
//								waitingset = new HashSet<>();
//								waitingmap.put(curr.obj, waitingset);
//							}
//							waitingset = waitingmap.get(curr.obj);
//							waitingset.add(waitingcn);
//							waitingmap.put(curr.obj, waitingset);
							
							CNode notifiedcn = new CNode(curr.obj,curr.u,curr.cid,"notified_entry",curr.me);
							
							cfg2ptsinsert(curr.u,notifiedcn);
							
							addedge(waitingcn,notifiedcn,"waitingsucc","waitingpred");
							pred = notifiedcn;
						}
													
					}		
				}
				
			}
			
			
			BriefUnitGraph cfgcurr = new BriefUnitGraph(curr.me.getActiveBody());
			List<Unit> currsucc = cfgcurr.getSuccsOf(curr.u);
			CNode succcn;
			
			
			for(Unit succunit:currsucc) {
				Stmt succstmt = (Stmt)succunit;
				
//				System.out.println("succ unit  is = " + succunit);
				if(succstmt.containsInvokeExpr()) {
//					System.out.println("HELLO");
					InstanceInvokeExpr succexpr = (InstanceInvokeExpr)succstmt.getInvokeExpr();
//					System.out.println("HELLO");
					if(succexpr instanceof VirtualInvokeExpr) {
//						System.out.println("virtual invoke STMT");
						Local lbasesucc = (Local)succexpr.getBase();
						SootMethod meth = succexpr.getMethod();
						
						
						
						pts = (PointsToSetInternal) pta.reachingObjects(lbasesucc);
						Set<String> ptsSet = new HashSet<>();
//						System.out.println("THE FOLLOWING ARE THE OBJECTS OF THIS LOCAL = ");
						P2SetVisitor vis = new P2SetVisitor() {

				               @Override
				               public void visit(Node n) {
				                /* Do something with node n*/
//				            	   System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>" + n +"<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
//				            	   System.out.println(n.getNumber());
//				            	   System.out.println(n.getType());
				            	   ptsSet.add(objMap.get(n));
				               }

				        };
				        (pts).forall(vis); //pti is the *PointsToSetInternal* set
				        

				        for(String pts:ptsSet) {
			        		
				        	succcn = new CNode(pts,succunit,curr.cid,meth.getName(),curr.me);
				        	
				        	cfg2ptsinsert(succunit,succcn);
							
							if(!inpro(succcn)) {
								queue.add(succcn);
//								succ.add(succcn);
							}
							succ.add(succcn);
							
							//updaing notifymap here
							if(meth.getName().equals("notify") || meth.getName().equals("notifyAll")) {
								if(!notifymap.containsKey(pts)) {
									Set<CNode> notifyset = new HashSet<>();
									notifymap.put(pts, notifyset);
								}
								
								Set<CNode> notifyset = notifymap.get(pts);
								
								notifyset.add(succcn);
								notifymap.put(pts, notifyset);
							}

				        }	
				        
				        
					}
					
					
					else if(succexpr instanceof SpecialInvokeExpr){
//						System.out.println("Special invoke STMT");
						succcn = new CNode("*",succunit,curr.cid,"<init>",curr.me);
						cfg2ptsinsert(succunit,succcn);
						if(!inpro(succcn)) {
							queue.add(succcn);
//							succ.add(succcn);
						}
						succ.add(succcn);
					}

				}
				
				else if(succstmt instanceof DefinitionStmt) {
//					System.out.println("DEFINITION STMT");
					succcn = new CNode("*",succunit,curr.cid,"definition",curr.me);
					cfg2ptsinsert(succunit,succcn);
					if(!inpro(succcn)) {
						queue.add(succcn);
//						succ.add(succcn);
					}
					succ.add(succcn);
				}
				
				else if(succstmt instanceof ReturnVoidStmt) {
//					System.out.println("RETURN VOID STMT");
					succcn = new CNode("*",succunit,curr.cid,"returnvoid",curr.me);
					cfg2ptsinsert(succunit,succcn);
					if(!inpro(succcn)) {
						queue.add(succcn);
//						succ.add(succcn);
					}
					succ.add(succcn);
				}
				
				else if(succstmt instanceof GotoStmt) {
//					System.out.println("GOTO STMT");
					succcn = new CNode("*",succunit,curr.cid,"goto",curr.me);
					cfg2ptsinsert(succunit,succcn);
					if(!inpro(succcn)) {
						queue.add(succcn);
//						succ.add(succcn);
					}
					succ.add(succcn);
				}
				
				else if(succstmt instanceof IfStmt) {
//					System.out.println("IF STMT");
					succcn = new CNode("*",succunit,curr.cid,"if",curr.me);
					cfg2ptsinsert(succunit,succcn);
					if(!inpro(succcn)) {
						queue.add(succcn);
//						succ.add(succcn);
					}
					succ.add(succcn);
				}
				
				else if(succstmt instanceof NopStmt) {
//					System.out.println("NOP STMT");
					succcn = new CNode("*",succunit,curr.cid,"nop",curr.me);
					cfg2ptsinsert(succunit,succcn);
					if(!inpro(succcn)) {
						queue.add(succcn);
//						succ.add(succcn);
					}
					succ.add(succcn);
				}
				
				else if(succstmt instanceof EnterMonitorStmt) {
//					System.out.println("ENTER MONITOR STMT");
					Value v = ((EnterMonitorStmt) succunit).getOp();
//					System.out.println(v.toString());
					pts = (PointsToSetInternal) pta.reachingObjects((Local) v);
					Set<String> ptsSet = new HashSet<>();
//					System.out.println("THE FOLLOWING ARE THE OBJECTS OF THIS LOCAL = ");
					P2SetVisitor vis = new P2SetVisitor() {

			               @Override
			               public void visit(Node n) {
			                /* Do something with node n*/
//			            	   System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>" + n +"<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
//			            	   System.out.println(n.getNumber());
//			            	   System.out.println(n.getType());
			            	   ptsSet.add(objMap.get(n));
			               }

			        };
			        (pts).forall(vis); //pti is the *PointsToSetInternal* set
			        
			        
			        for(String lobj:ptsSet) {
						succcn = new CNode(lobj,succunit,curr.cid,"entry",curr.me);
						cfg2ptsinsert(succunit,succcn);
						if(!inpro(succcn)) {
							queue.add(succcn);
//							succ.add(succcn);
//							if(!queuemap.containsKey(lobj)) {
//								Set<CNode> monset = new HashSet<>();
//								queuemap.put(lobj, monset);
//								lockcount.put(lobj, 0);
//							}
							monitorset.add(succcn);
						}
						succ.add(succcn);
					}
			        
				}
				
				
				
				else if(succstmt instanceof ExitMonitorStmt) {
//					System.out.println("EXIT MONITOR STMT");
					Value v = ((ExitMonitorStmt) succunit).getOp();
					pts = (PointsToSetInternal) pta.reachingObjects((Local) v);
					Set<String> ptsSet = new HashSet<>();
//					System.out.println("THE FOLLOWING ARE THE OBJECTS OF THIS LOCAL = ");
					P2SetVisitor vis = new P2SetVisitor() {

			               @Override
			               public void visit(Node n) {
			                /* Do something with node n*/
//			            	   System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>" + n +"<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
//			            	   System.out.println(n.getNumber());
//			            	   System.out.println(n.getType());
			            	   ptsSet.add(objMap.get(n));
			               }

			        };
			        (pts).forall(vis); //pti is the *PointsToSetInternal* set
			        
			        
			        for(String lobj:ptsSet) {
						succcn = new CNode(lobj,succunit,curr.cid,"exit",curr.me);
						cfg2ptsinsert(succunit,succcn);
						all.add(succunit);
						if(!inpro(succcn)) {
							queue.add(succcn);
//							succ.add(succcn);
						}
						succ.add(succcn);
					}
				}
				
				
				
				else if(succstmt instanceof ThrowStmt) {
//					System.out.println("THROW STMT");
					succcn = new CNode("*",succunit,curr.cid,"throw",curr.me);
					cfg = new BriefUnitGraph(curr.me.getActiveBody());
					List<Unit> li = cfg.getSuccsOf(curr.u);
//					System.out.println(cfg.getHeads());
					List<Unit> lii ;
					Set<Unit> liii = new HashSet<>();
//					System.out.println("))))))))))))))))))))))))))))))))))))))))" + cfg.getSuccsOf(li.iterator().next()));
					lii = cfg.getHeads();
					for(Unit u:lii) {
						liii.addAll(cfg.getSuccsOf(u));
					}
//					System.out.println(liii);
					cfg2ptsinsert(succunit,succcn);
					if(!inpro(succcn)) {
						queue.add(succcn);
//						succ.add(succcn);
					}
					succ.add(succcn);
				}

			}
			
			
			margin();
			
			
			
//			System.out.println(all.size());
//			System.out.println("------------------------SUCCESSORS---------------------------");
//			for(CNode cn:succ) {
//				printvertex(cn);
//			}
//			System.out.println("PRED IS - ");
//			printvertex(pred);
//			
			for(CNode succe:succ) {
				addedge(pred,succe,"normal","normalpred");
			}
			
			processed.add(curr);
		}
		
		
//		printMap(pegSuccs);
		
		
		
		
//		for(CNode cn:monitorset) {
//			printvertex(cn);
//			String obj = cn.obj;
//			Set<CNode> mset = null;
//			if(!monitormap.containsKey(obj)) {
//				mset = new HashSet<>();
//				monitormap.put(obj, mset);
//			}
//			mset = monitormap.get(obj);
//			System.out.print("NOW MONITOR SET");
//			System.out.println(">><<");
//			System.out.println("BEFORE = ");
//			for(CNode cnn : mset) {
//				printvertex(cnn);
//			}
//			mset.addAll(reach(cn));
//			System.out.println("AFTER = ");
//			for(CNode cnn : mset) {
//				printvertex(cnn);
//			}
//			monitormap.put(obj, mset);
//			System.out.println("J");
//		}
//		
//	
//		for(Map.Entry<String, Set<CNode>> entry:monitormap.entrySet()) {
//			System.out.println(entry.getKey());
//			for(CNode cn:entry.getValue()) {
//				printvertex(cn);
//			}
//		}
		
		//////////////////////////////////////////////////////////////////////////////////////////////////////
		//this portion is just for creating monitormap , working//
		for(CNode cn:monitorset) {
//			printvertex(cn);
		}
		
		monitormapupdater(monitorset);
//		System.out.println("_______MONITOR MAP PRINTING__________");
		for(Map.Entry<String, Set<CNode>> entry:monitormap.entrySet()) {
//			System.out.println("KEY = " + entry.getKey());
			for(CNode cn:entry.getValue()) {
//				printvertex(cn);
			}
		}
		
		////////////////////////////////////////////////////////////////////////////////////////////////////////
//		System.out.println("JJJJJJJJJJJJJJJJJJJJJJJJJJJJJJJJJJJJJ");
//		Set<CNode> sett = reachablestart("main");
//		for(CNode cc:sett) {
//			printvertex(cc);
//		}
		
//		//////////////////////////////////////////////////////////////////////////////////////////////////////////
		
		analyze();
		
		
//		System.out.println(":::::::::::::::::::::::::::::::::::::::::::::+++++++++++++++++++++++++:+++++++++++++++");
		for(Map.Entry<CNode, Set<CNode>> entry:M.entrySet()) {
//			printvertex(entry.getKey());
			for(CNode cb:entry.getValue()) {
//				printvertex(cb);
			}
		}
		
		
		for(int i = 0;i < A3.queryList.size();i ++) {
			MhpQuery q = A3.queryList.get(i);
			String var = q.getVar();
			String field = q.getField();
			A3.answers[i] = "No";
			//System.out.println(ClassName);
			//System.out.println(MethodName);
			for(SootMethod m :setOfMethods) {
				Body arg = m.getActiveBody();
				cfg = new BriefUnitGraph(arg);
				PatchingChain<Unit> li = arg.getUnits();
				for(Unit u:li) {
					Stmt st = (Stmt)u;
					if(st instanceof DefinitionStmt) {
						Value lhs = ((DefinitionStmt) st).getLeftOp();
						Value rhs = ((DefinitionStmt) st).getRightOp();
						if(lhs instanceof InstanceFieldRef && !(rhs instanceof InstanceFieldRef)) {
							InstanceFieldRef IFR = (InstanceFieldRef)lhs;
							Value l = IFR.getBase();
							SootField f = IFR.getField();
							String r = rhs.toString();
							if(!l.toString().equals(var) || !f.toString().equals(field)) continue;
							Set<CNode> set = cfg2pts.get(u);
							for(CNode cn1:set) {
								Set<CNode> set1 = M.get(cn1);
								
								for(CNode cn2:set1) {
									if(cn2.u!=null) {
										Unit u1 = cn2.u;
										Stmt st1 = (Stmt)u1;
										if(st1 instanceof DefinitionStmt) {
											Value lhs1 = ((DefinitionStmt) st1).getLeftOp();
											Value rhs1 = ((DefinitionStmt) st1).getRightOp();
											if(!(lhs instanceof InstanceFieldRef) && (rhs instanceof InstanceFieldRef)) {
												if(cn1.obj.equals(cn2.obj))
													A3.answers[i] = "Yes";
											}
										}
									}
								}
							}
						}
					}
					
					
					
				}
			}
			
		}
		

	}
}
