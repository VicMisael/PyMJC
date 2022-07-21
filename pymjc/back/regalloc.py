from __future__ import annotations
from abc import abstractmethod
from ast import Return
import sys
import queue
from typing import List, Set


from pymjc.back import assem, flowgraph, graph
from pymjc.front import frame, temp

class RegAlloc (temp.TempMap):
    def __init__(self, frame: frame.Frame, instr_list: assem.InstrList):
        self.frame: frame.Frame = frame
        self.instrs: assem.InstrList = instr_list
        self.pre_colored_nodes: Set[graph.Node]=[]
        self.normal_colored_nodes: Set[graph.Node]=[]
        self.initial_nodes: Set[graph.Node]=[]
        self.spill_nodes: Set[graph.Node]=[]
        self.coalesce_nodes:Set[graph.Node]=[]
        self.node_stack: List[graph.Node]=[]
        self.simplify_work_list: Set[graph.Node]=[]
        self.freeze_work_list: Set[graph.Node]=[]
        self.spill_work_list: Set[graph.Node]=[]
        self.coalesce_move_nodes: Set[graph.Node]=[]
        self.constrain_move_nodes: Set[graph.Node]=[]
        self.freeze_move_nodes: Set[graph.Node]=[]
        self.worklist_move_nodes: Set[graph.Node]=[]
        self.active_move_nodes: Set[graph.Node]=[]
        self.spill_cost:dict[graph.Node,int]=[]
        self.adjacent_sets:Set[Edge]=[]
        self.adjacent_list:dict[graph.Node,Set[graph.Node]]=[]
        self.liveness_output:Liveness={}
        self.assem_flow_graph:flowgraph.AssemFlowGraph={}
        self.move_nodes_list: dict[graph.Node, Set[graph.Node] ] =[]
        self.node_degree_table: dict[graph.Node, int ] = []
        self.node_alias_table: dict[graph.Node, graph.Node] = []
        self.node_color_table: dict[graph.Node, graph.Node] = []
        self.generated_spill_temps:Set[temp.Temp]=[]
        self.main_procedure()

    def main_procedure(self):
        shallcontinue:bool=True
        while(shallcontinue):
            shallcontinue=False
            self.liveness_analysis()
            self.init()
            self.build()
            self.make_work_list()

            while True:
                if(len(self.simplify_work_list) != 0):
                    self.simplify()
                elif(len(self.worklist_move_nodes) != 0):
                    self.coalesce()
                elif(len(self.freeze_work_list) != 0):
                    self.freeze()
                elif(len(self.spill_work_list) != 0):
                    self.select_spill()

                if not(len(self.simplify_work_list) != 0 or len(self.worklist_move_nodes) != 0 or len(self.freeze_work_list) != 0 or len(self.spill_work_list) != 0):
                    break
            self.assign_colors()

            if(len(self.spill_nodes) != 0):
                self.rewrite_program() 
                shallcontinue = True

        self.final_step() 

    def liveness_analysis(self):
        self.assem_flow_graph = flowgraph.AssemFlowGraph(self.instrs)

        self.liveness_output = Liveness(self.assem_flow_graph)
    
    def init(self):

        self.pre_colored_nodes.clear()
        self.normal_colored_nodes.clear()

        self.initial_nodes.clear()
        self.spill_nodes.clear()
        self.coalesce_nodes.clear()

  
        self.node_stack.clear()

      
        self.simplify_work_list.clear()
        self.freeze_work_list.clear()
        self.spill_work_list.clear()

      
        self.coalesce_move_nodes.clear()
        self.constrain_move_nodes.clear()
        self.freeze_move_nodes.clear()
        self.active_move_nodes.clear()

        self.spill_cost.clear()

        self.adjacent_sets.clear()
        self.adjacent_list.clear()

        self.move_nodes_list.clear()

        self.node_alias_table.clear()
        self.node_color_table.clear()
        self.node_degree_table.clear()


        counter = 0

        MAX_VALUE: int = sys.maxsize

        while( counter < len(self.frame.registers())):

            temp: temp.Temp = self.frame.registers()[counter]
            node = graph.Node = self.liveness_output.tnode(temp)

            self.pre_colored_nodes.add(node)
            self.spill_cost[node] = MAX_VALUE

            self.node_color_table[node] = node
            self.node_degree_table[node] = 0
            
            counter+=1

        nodeList: graph.NodeList = self.liveness_output.nodes()

        while(nodeList is not None):
            node: graph.Node = nodeList.head

            if(not(self.pre_colored_nodes.__contains__(node))):
                self.initial_nodes.add(node)

                if(self.generated_spill_temps.__contains__(self.liveness_output.gtemp(node))):
                    self.spill_cost[node] = MAX_VALUE
                elif(not(self.pre_colored_nodes.__contains__(node))):
                    self.spill_cost[node] = 1    

                self.node_degree_table[node] = 0

            nodeList = nodeList.tail  
    def build(self):
        nodeList: graph.NodeList = self.assem_flow_graph.nodes()

        while(nodeList is not None):

            node: graph.Node = nodeList.head

            live : set[temp.Temp] = self.liveness_output.out(node)

            isMoveInstruction: bool = self.assem_flow_graph.is_move(node)

            if(isMoveInstruction):
                uses: temp.TempList = self.assem_flow_graph.use(node)

                while(uses is not None):
                    live.remove(uses.head)
                    uses = uses.tail
                
                uses: temp.TempList = self.assem_flow_graph.use(node)

                while(uses is not None):
                    self.move_nodes_list(self.liveness_output.tnode(uses.head))[node] = node ##adicionar nó ao hashtable
                    uses = uses.tail

                self.worklist_move_nodes.add(node)

            defs: temp.TempList = self.assem_flow_graph.deff(node)

            while(defs is not None):
                live.add(defs.head)  

                defs = defs.tail  

            defs: temp.TempList = self.assem_flow_graph.deff(node)

            while(defs is not None):
                
                for live_temp in live:
                    self.add_edge(live_temp, defs.head) #implementar add_edge

                defs = defs.tail 

            nodeList = nodeList.tail
     
    def make_work_list(self):
        K: int = len(self.pre_colored_nodes)

        nodeIterator = iter(self.initial_nodes)
       

        while(next(nodeIterator, None) is not None):
            n: graph.Node = next(nodeIterator)

            self.initial_nodes.remove(nodeIterator)  

            if(self.node_degree_table(n) >= K):
                self.spill_work_list.add(n)
            elif(self.move_related(n)): ##implementar o metodo
                self.freeze_work_list.add(n)
            else:
                self.simplify_work_list.add(n)     

    def simplify(self):
        temporaryIterator = iter(self.simplify_work_list)
        n: graph.Node = next(temporaryIterator)

        self.simplify_work_list.remove(temporaryIterator)
        
        self.node_stack.append(n)
        
        for no in n.adj:
            self.decrement_degree(no)
        
    def coalesce(self):
        temporary_iterator = iter(self.simplify_work_list)
        m:graph.Node=None
        next_val= next(temporary_iterator,None)
        if( next_val is not None):
            m=next_val
        
        x:graph.Node=self.get_alias(self.liveness_output.tnode(self.assem_flow_graph.instr(m).deff().head))    
        y:graph.Node=self.get_alias(self.liveness_output.tnode(self.assem_flow_graph.instr(m).use().head))
        u:graph.Node
        v:graph.Node
        if(y in self.pre_colored_nodes):
            u=y
            v=x
        else:
            u=x
            v=y
        
        e:Edge=Edge.get_edge(u,v)

        self.worklist_move_nodes.remove(m)

        if(u==v):
            self.coalesce_move_nodes.add(m)
        elif(u in self.pre_colored_nodes or e in self.adjacent_sets):
            self.constrain_move_nodes.add(m)
            self.add_work_list(u)
            self.add_work_list(v)
        elif(self.coalesce_auxiliar_first_checking(u,v) or self.coalesce_auxiliar_second_checking):
            self.combine(u,v)
            self.add_work_list(u)
        else:
            self.active_move_nodes.add(m)
            
    def OK(self,t:graph.Node,r:graph.Node)->bool:
        k:int = len(self.pre_colored_nodes)
        result:bool = t in self.pre_colored_nodes or self.node_degree_table.get(t)<k or Edge.get_edge(t,r) in self.adjacent_sets
        return result

    def conservative(self,nodes:Set[graph.Node]):
        k:int =0
        K:int=len(self.pre_colored_nodes)
        for n in nodes:
            if(self.node_degree_table.get(n)>=K):
                k=k+1
        return k<K

    def Adjacent(self,n:graph.Node)->Set[graph.Node]:

        return self.adjacent_list.get(n).discard(self.coalesce_nodes.union(self.node_stack))


    def coalesce_auxiliar_first_checking(self,u:graph.Node,v:graph.Node)->bool:
        if(u not in self.pre_colored_nodes):
            return False
        for t in self.Adjacent(u):
            if(not self.OK(t,u)):  
                return False
            
        return True
        
    def coalesce_auxiliar_second_checking(self,u:graph.Node,v:graph.Node)->bool:
        if(u in self.pre_colored_nodes):
            return False

        return self.conservative(self.Adjacent(u).union(self.Adjacent(v)))
            
    def is_move_related(self,n:graph.Node)->bool:
        pass

    def add_work_list(self,u:graph.Node):
        pass
    def freeze(self):
        pass
    def select_spill(self):
        pass
    def assign_colors(self):
        pass
    def rewrite_program(self):
        pass
    def final_step(self):
        pass
    def add_edge(self,u_temp:temp.Temp,v_temp:temp.Temp):
        pass
    def decrement_degree(self,n:graph.Node):
        pass
    def get_alias(n:graph.Node):
        pass

    def temp_map(self, temp: temp.Temp) -> str:
        str = self.frame.temp_map(temp)

        if(str is None):
            str = self.frame.temp_map(self.liveness_output.gtemp(self.node_color_table.get(self.liveness_output.tnode(temp))))
        
        return temp.to_string()

    def move_related(n:graph.Node):
        pass

    def get_alias(n:graph.Node):
        pass
class Color(temp.TempMap):
    def __init__(self, ig: InterferenceGraph, initial: temp.TempMap, registers: temp.TempList):
        #TODO
        pass
    
    def spills(self) -> temp.TempList:
        #TODO
        return None

    def temp_map(self, temp: temp.Temp) -> str:
        #TODO
        return temp.to_string()

class InterferenceGraph(graph.Graph):
    
    @abstractmethod
    def tnode(self, temp:temp.Temp) -> graph.Node:
        pass

    @abstractmethod
    def gtemp(self, node: graph.Node) -> temp.Temp:
        pass

    @abstractmethod
    def moves(self) -> MoveList:
        pass
    
    def spill_cost(self, node: graph.Node) -> int:
      return 1


class Liveness (InterferenceGraph):

    def __init__(self, flow: flowgraph.FlowGraph):
        self.live_map = {}
        
        #Flow Graph
        self.flowgraph: flowgraph.FlowGraph = flow
        
        #IN, OUT, GEN, and KILL map tables
        #The table maps complies with: <Node, Set[Temp]>
        self.in_node_table = {}
        self.out_node_table = {}
        self.gen_node_table = {}
        self.kill_node_table = {}

        #Util map tables
        #<Node, Temp>
        self.rev_node_table = {}
        #<Temp, Node>
        self.map_node_table = {}
        
        #Move list
        self.move_list: MoveList = None

        self.build_gen_and_kill()
        self.build_in_and_out()
        self.build_interference_graph()
    
    def add_ndge(self, source_node: graph.Node, destiny_node: graph.Node):
        if (source_node is not destiny_node and not destiny_node.comes_from(source_node) and not source_node.comes_from(destiny_node)):
            super.add_edge(source_node, destiny_node)

    def show(self, out_path: str) -> None:
        if out_path is not None:
            sys.stdout = open(out_path, 'w')   
        node_list: graph.NodeList = self.nodes()
        while(node_list is not None):
            temp: temp.Temp = self.rev_node_table.get(node_list.head)
            print(temp + ": [ ")
            adjs: graph.NodeList = node_list.head.adj()
            while(adjs is not None):
                print(self.rev_node_table.get(adjs.head) + " ")
                adjs = adjs.tail

            print("]")
            node_list = node_list.tail
    
    def get_node(self, temp: temp.Temp) -> graph.Node:
      requested_node: graph.Node = self.map_node_table.get(temp)
      if (requested_node is None):
          requested_node = self.new_node()
          self.map_node_table[temp] = requested_node
          self.rev_node_table[requested_node] = temp

      return requested_node

    def node_handler(self, node: graph.Node):
        def_temp_list: temp.TempList = self.flowgraph.deff(node)
        while(def_temp_list is not None):
            got_node: graph.Node  = self.get_node(def_temp_list.head)

            for live_out in self.out_node_table.get(node):
                current_live_out = self.get_node(live_out)
                self.add_edge(got_node, current_live_out)

            def_temp_list = def_temp_list.tail

  
    def move_handler(self, node: graph.Node):
        source_node: graph.Node  = self.get_node(self.flowgraph.use(node).head)
        destiny_node: graph.Node = self.get_node(self.flowgraph.deff(node).head)

        self.move_list = MoveList(source_node, destiny_node, self.move_list)
    
        for temp in self.out_node_table.get(node):
            got_node: graph.Node = self.get_node(temp)
            if (got_node is not source_node ):
                self.addEdge(destiny_node, got_node)


    def out(self, node: graph.Node) -> Set[temp.Temp]:
        temp_set = self.out_node_table.get(node)
        return temp_set


    def tnode(self, temp:temp.Temp) -> graph.Node:
        node: graph.Node = self.map_node_table.get(temp)
        if (node is None ):
            node = self.new_node()
            self.map_node_table[temp] = node
            self.rev_node_table[node] = temp
        
        return node

    def gtemp(self, node: graph.Node) -> temp.Temp:
        temp: temp.Temp = self.rev_node_table.get(node)
        return temp

    def moves(self) -> MoveList:
        return self.move_list

    def build_gen_and_kill(self):
        kill_node_hash_table:dict[graph.Node,Set(temp.Temp)]=[]
        gen_node_hash_table:dict[graph.Node,Set(temp.Temp)]=[]
        nodelist:graph.NodeList=self.flowgraph.nodes()
        head:graph.Node=nodelist.head
        while (head is not None):
            nodelist=nodelist.tail
            head=nodelist.head
            temporary_kill:Set[graph.Node]=[]
            temporary_gen:Set[graph.Node]=[]
            temp_list:temp.TempList= self.flowgraph.use(head)
            while (temp_list is not None):
                temporary_gen.add(temp_list.head)
                temp_list=temp_list.tail
            temp_list_kill:temp.TempList= self.flowgraph.use(head)
            while (temp_list_kill is not None):
                temporary_kill.add(temp_list.head)
                temp_list_kill=temp_list_kill.tail
            kill_node_hash_table[nodelist.head]=temporary_kill
            gen_node_hash_table[nodelist.head]=temporary_gen

    def build_in_and_out(self):
        nodelist:graph.NodeList=self.flowgraph.nodes()
        head:graph.Node=nodelist.head
        while (head is not None):
            self.in_node_table[head]=Set[temp.Temp]
            self.out_node_table[head]=Set[temp.Temp]
            nodelist=nodelist.tail
            head:graph.Node=nodelist.head
    

        while True:
            nodelist:graph.NodeList=self.flowgraph.nodes()
            head:graph.Node=nodelist.head

            while (head is not None):
                # in e out
                in_original:Set[temp.Temp]=self.in_node_table[head]
                out_original:Set[temp.Temp]=self.out_node_table[head]
                # in' e out'
                in_set:Set[temp.Temp]=in_original
                out_set:Set[temp.Temp]=out_original
                # in[n] ← use[n] ∪ (out[n] − def[n])
                self.in_node_table[head]=self.setof(self.flowgraph.use(head)).union(out_original.difference(self.setof(self.flowgraph.deff())))
                # out[n] ←  s∈succ[n] in[s]
                # para da s de succ em in, se eu tenho um conjunto de todos os succ e todos os in, o que tem nos 2 é a intereseção de ambos
                self.out_node_table[head]=self.setofnode(head.succ()).intersection(in_original)
                
                if((not all(elem in in_set for elem in self.in_node_table[head])) or
                (not all(elem in out_set for elem in self.out_node_table[head]))):
                        break
                else:
                    nodelist=nodelist.tail
                    head=nodelist.head

    def setof(self,list:temp.TempList)->Set[temp.Temp]:
        _set:Set[temp.Temp]=set()
        head:temp.Temp=list.head
        tail:temp.TempList=list.tail
        
        while (head is not None):
            _set.add(head)
            head=tail.head
            tail=tail.tail
        return _set

    def setofnode(self,list:graph.NodeList)->Set[graph.Node]:
        _set:Set[graph.Node]=set()
        head:graph.Node=list.head
        tail:graph.NodeList=list.tail
        
        while (head is not None):
            _set.add(head)
            head=tail.head
            tail=tail.tail
        return _set

    def build_interference_graph(self):
        nodeList: graph.NodeList = self.flowgraph.nodes()

        while nodeList.head != None:
            if(self.flowgraph.is_move(nodeList.head)):
                self.move_handler(nodeList.head())
            else:
                self.node_handler(nodeList.head())
            nodeList = nodeList.tail
        return None


class Edge():

    edges_table = []

    def __init__(self):
        super.__init__()
    
    def get_edge(self, origin_node: graph.Node, destiny_node: graph.Node) -> Edge:
        
        origin_table = Edge.edges_table.get(origin_node)
        destiny_table = Edge.edges_table.get(destiny_node)
        
        if (origin_table is None):
            origin_table = []
            Edge.edges_table[origin_node] = origin_table

        if (destiny_table is None):
            destiny_table = []
            Edge.edges_table[destiny_node] = destiny_table
        
        requested_edge: Edge  = origin_table.get(destiny_node)

        if(requested_edge is None):
            requested_edge = Edge()
            origin_table[destiny_node] = requested_edge
            destiny_table[origin_node] = requested_edge

        return requested_edge



class MoveList():

   def __init__(self, s: graph.Node, d: graph.Node, t: MoveList):
      self.src: graph.Node = s
      self.dst: graph.Node = d
      self.tail: MoveList = t
