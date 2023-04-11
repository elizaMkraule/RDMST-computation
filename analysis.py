# Eliza Marija Kraule
# emk6

import graphviz
from typing import Tuple
from collections import *
from copy import *



def bfs(graph, startnode):
    """
        Perform a breadth-first search on digraph graph starting at node startnode.

        Arguments:
        graph -- directed graph
        startnode - node in graph to start the search from

        Returns:
        The distances from startnode to each node
    """
    dist = {}

    # Initialize distances
    for node in graph:
        dist[node] = float('inf')
    dist[startnode] = 0

    # Initialize search queue
    queue = deque([startnode])

    # Loop until all connected nodes have been explored
    while queue:
        node = queue.popleft()
        for nbr in graph[node]:
            if dist[nbr] == float('inf'):
                dist[nbr] = dist[node] + 1
                queue.append(nbr)
    return dist


def compute_rdmst(graph, root):
    """
        This function checks if:
        (1) root is a node in digraph graph, and
        (2) every node, other than root, is reachable from root
        If both conditions are satisfied, it calls compute_rdmst_helper
        on (graph, root).

        Since compute_rdmst_helper modifies the edge weights as it computes,
        this function reassigns the original weights to the RDMST.

        Arguments:
        graph -- a weighted digraph in standard dictionary representation.
        root -- a node id.

        Returns:
        An RDMST of graph rooted at r and its weight, if one exists;
        otherwise, nothing.
    """

    if root not in graph:
        print("The root node does not exist")
        return

    distances = bfs(graph, root)
    for node in graph:
        if distances[node] == float('inf'):
            print("The root does not reach every other node in the graph")
            return

    rdmst = compute_rdmst_helper(graph, root)

    # reassign the original edge weights to the RDMST and computes the total
    # weight of the RDMST
    rdmst_weight = 0
    for node in rdmst:
        for nbr in rdmst[node]:
            rdmst[node][nbr] = graph[node][nbr]
            rdmst_weight += rdmst[node][nbr]

    return (rdmst, rdmst_weight)


def compute_rdmst_helper(graph, root):
    """
        Computes the RDMST of a weighted digraph rooted at node root.
        It is assumed that:
        (1) root is a node in graph, and
        (2) every other node in graph is reachable from root.

        Arguments:
        graph -- a weighted digraph in standard dictionary representation.
        root -- a node in graph.

        Returns:
        An RDMST of graph rooted at root. The weights of the RDMST
        do not have to be the original weights.
        """

    # reverse the representation of graph
    rgraph = reverse_digraph_representation(graph)

    # Step 1 of the algorithm
    modify_edge_weights(rgraph, root)

    # Step 2 of the algorithm
    rdst_candidate = compute_rdst_candidate(rgraph, root)

    # compute a cycle in rdst_candidate
    cycle = compute_cycle(rdst_candidate)

    # Step 3 of the algorithm
    if not cycle:
        return reverse_digraph_representation(rdst_candidate)
    else:
        # Step 4 of the algorithm

        g_copy = deepcopy(rgraph)
        g_copy = reverse_digraph_representation(g_copy)

        # Step 4(a) of the algorithm
        (contracted_g, cstar) = contract_cycle(g_copy, cycle)
        # cstar = max(contracted_g.keys())

        # Step 4(b) of the algorithm
        new_rdst_candidate = compute_rdmst_helper(contracted_g, root)

        # Step 4(c) of the algorithm
        rdmst = expand_graph(reverse_digraph_representation(rgraph), new_rdst_candidate, cycle, cstar)

        return rdmst


def reverse_digraph_representation(graph: dict) -> dict:
    """
    This function computes a reverse digraph from a given digraph
    input: a weighted digraph graph in the standard representation
    returns: exactly the same weighted digraph graph but in the reversed representation.
    """
    rdigraph = dict()
    for head in graph.keys():
        rdigraph[head] = {}
        for item in graph.items():
            for tail in item[1].keys():
                if head == tail:
                    weight = item[1].get(tail)
                    rdigraph[head].update({item[0]: weight})
    return rdigraph


def modify_edge_weights(rgraph: dict, root: int) -> None:  
    """
    This function modifies the weights of all edges in rgraph according to Lemma 2
    input:  weighted digraph graph in the reversed representation
            and a node root
    output: nothing
    """
    nodes = rgraph.keys()
    for node in nodes:
        children = rgraph.get(node)
        if len(children) > 0:
            minimum = min(children.values())
            for child in children:
                rgraph.get(node).update({child: children.get(child) - minimum})


def compute_rdst_candidate(rgraph: dict, root: int) -> dict:
    """
        This function computes an RDST candidate based on Lemma 1 of weighted digraph graph.
        input:
            weighted digraph in reversed representation
            root node
        output: RDST candidate in reversed representation
    """
    candidate = {}
    added = False
    for node in rgraph.keys():
        if node == root:
            candidate[node]= {}
        else:
            children = rgraph.get(node)
            if len(children) > 0:
                minimum = min(children.values())
                for child in children:
                    if children.get(child) == minimum and not added:
                        candidate.update({node: {child: children.get(child)}})
                        added = True
                added = False
    return candidate


def is_cycle_helper(rdst_candidate: dict, visited: list, current: int) -> list:
    """
     helper function for compute_cycle

    """
    if [current, True] in visited:
        cycle = []
        for i in range(len(visited)):
            if visited[i][1] == True:
                cycle.append(visited[i][0])
        return [True, cycle]

    visited.append([current, True])
    flag = [False]
    children = rdst_candidate.get(current, [])
    for child in children:
        flag = is_cycle_helper(rdst_candidate, visited, child)
        if flag[0] == True:
            return [True, flag[1]]
    visited.pop()
    return [False, []]


def is_cycle(rdst_candidate: dict) -> bool:
    """
           helper function for compute_cycle

           """
    nodes = rdst_candidate.keys()
    visited = []
    for node1 in nodes:
        ls = [node1, False]
        visited.append(ls)

    flag = [False]
    for node in nodes:
        index = visited.index([node, False])
        visited[index] = [node, True]  # mark as visited
        children = rdst_candidate.get(node)
        for child in children:
            flag = is_cycle_helper(rdst_candidate, visited, child)
            if flag[0] == True:
                return flag[1]
        visited[index] = [node, False]  # mark as unvisited
    return []


def compute_cycle(rdst_candidate: dict) -> tuple:
    """
     this function checks graph for cycle and finds it if it exists returning a tuple of the nodes of the cycle

    input:
        rdst_candidate-RDST candidate based on Lemma 1 of weighted digraph graph.
    output:
         cycle- a tuple of nodes in the cycle or none if cycle doesnt exist

   """
    cycle = tuple((is_cycle(reverse_digraph_representation(rdst_candidate))))
    if len(cycle) == 0:
        return None
    else:
        return cycle


def contract_cycle(graph: dict, cycle: tuple) -> Tuple[dict, int]:
    """
    input:
        a weighted digraph graph in the standard representation
        a tuple representing a cycle
    output:
    returns (contracted_graph, cstar)
        contracted_graph is the digraph that results from contracting cycle
        cstar is the number of the new nodes added to replace the cycle
 """

    contracted_graph = {}
    contracted_nodes = set(cycle)  # create set of nodes in cycle
    cstar = max(graph.keys()) + 1  # create cstar node

    for node in graph.keys():
        if node in contracted_nodes:
            contracted_graph[cstar] = {}  # add cstar as a new node
        else:
            contracted_graph[node] = {}

        for child in graph.get(node, {}):
            if child in contracted_nodes:
                # add edge to cstar with minimum weight
                contracted_graph[node][cstar] = min(
                    graph.get(node).get(child),
                    contracted_graph[node].get(cstar, float('inf'))
                )
            elif node in contracted_nodes:
                # add edge from cstar to child
                contracted_graph[cstar][child] = graph.get(node).get(child)
            else:
                # add edge between non-cyclic nodes
                contracted_graph[node][child] = graph.get(node).get(child)

    return (contracted_graph, cstar)


def expand_graph(graph: dict, rdst_candidate: dict, cycle: tuple, cstar: int) -> dict:
    """
      input:
          graph-a weighted digraph graph in the standard representation
          cycle-a tuple representing a cycle
          rdst-candidate-RDST candidate based on Lemma 1 of weighted digraph graph.
          cstar-cstar is the number of the new node added to replace the cycle
      output:
      returns rdmst - rooted directed minimum spanning tree
   """

    rdmst = {}

    # first add all nodes from graph to the rdmst

    for nodes in graph:
        rdmst[nodes] = {}

    tail = None  # intialize tail to none

    # get node in candidate and get its child
    for node in rdst_candidate:
        for child in rdst_candidate[node]:

            # if the node and its child is not cstar, then add the node and an edge to the node
            if node != cstar and child != cstar:
                rdmst[node][child] = graph[node][child]

            # if its child is cstar then find the min edge which connects to the cycle and add the edge to the rdmst
            if child == cstar:
                min_weight = float('inf')
                min_node = None
                for in_node, weight in graph[node].items():
                    if in_node in cycle:
                        if weight < min_weight:
                            min_weight = weight
                            min_node = in_node
                            tail = in_node
                rdmst[node][min_node] = min_weight
            # nodes going out of cycle
            # if the node is cstar, find the node it replaced
            if node == cstar:
                min_weight = float('inf')
                min_node = None
                for out_node in cycle:
                    if child in graph[out_node]:
                        weight = graph[out_node][child]
                        if weight < min_weight:
                            min_weight = weight
                            min_node = out_node
                rdmst[min_node][child] = min_weight

    # add in the edges inside the cycle

    for nod in cycle:
        for edges in graph[nod]:
            a = graph[nod][edges]
            if a == 0 and edges != tail and (edges in cycle) and nod != edges:
                rdmst[nod][edges] = 0
    return rdmst


def infer_transmap(gen_data, epi_data, patient_id):
    """
        Infers a transmission map based on genetic
        and epidemiological data rooted at patient_id

        Arguments:
        gen_data -- filename with genetic data for each patient
        epi_data -- filename with epidemiological data for each patient
        patient_id -- the id of the 'patient 0'

        Returns:
        The most likely transmission map for the given scenario as the RDMST
        of a weighted, directed, complete digraph
        """

    complete_digraph = construct_complete_weighted_digraph(gen_data, epi_data)
    return compute_rdmst(complete_digraph, patient_id)


def read_patient_sequences(filename):
    """
        Turns the bacterial DNA sequences (obtained from patients) into a list containing tuples of
        (patient ID, sequence).

        Arguments:
        filename -- the input file containing the sequences

        Returns:
        A list of (patient ID, sequence) tuples.
        """
    sequences = []
    with open(filename) as f:
        line_num = 0
        for line in f:
            if len(line) > 5:
                patient_num, sequence = line.split("\t")
                sequences.append((int(patient_num), ''.join(e for e in sequence if e.isalnum())))
    return sequences


def read_patient_traces(filename):
    """
        Reads the epidemiological data file and computes the pairwise epidemiological distances between patients

        Arguments:
        filename -- the input file containing the sequences

        Returns:
        A dictionary of dictionaries where dict[i][j] is the
        epidemiological distance between i and j.
    """
    trace_data = []
    patient_ids = []
    first_line = True
    with open(filename) as f:
        for line in f:
            if first_line:
                patient_ids = line.split()
                patient_ids = list(map(int, patient_ids))
                first_line = False
            elif len(line) > 5:
                trace_data.append(line.rstrip('\n'))
    return compute_pairwise_epi_distances(trace_data, patient_ids)


def compute_pairwise_gen_distances(sequences, distance_function):
    """
        Computes the pairwise genetic distances between patients (patients' isolate genomes)

        Arguments:
        sequences -- a list of sequences that correspond with patient id's
        distance_function -- the distance function to apply to compute the weight of the
        edges in the returned graph

        Returns:
        A dictionary of dictionaries where gdist[i][j] is the
        genetic distance between i and j.
        """
    gdist = {}
    cultures = {}

    # Count the number of differences of each sequence
    for i in range(len(sequences)):
        patient_id = sequences[i][0]
        seq = sequences[i][1]
        if patient_id in cultures:
            cultures[patient_id].append(seq)
        else:
            cultures[patient_id] = [seq]
            gdist[patient_id] = {}
    # Add the minimum sequence score to the graph
    for pat1 in range(1, max(cultures.keys()) + 1):
        for pat2 in range(pat1 + 1, max(cultures.keys()) + 1):
            min_score = float("inf")
            for seq1 in cultures[pat1]:
                for seq2 in cultures[pat2]:
                    score = distance_function(seq1, seq2)
                    if score < min_score:
                        min_score = score
            gdist[pat1][pat2] = min_score
            gdist[pat2][pat1] = min_score
    return gdist


### HELPER FUNCTIONS ###

def find_first_positives(trace_data):
    """
        Finds the first positive test date of each patient
        in the trace data.
        Arguments:
        trace_data -- a list of data pertaining to location
        and first positive test date
        Returns:
        A dictionary with patient id's as keys and first positive
        test date as values. The date numbering starts from 0 and
        the patient numbering starts from 1.
        """
    first_pos = {}
    for pat in range(len(trace_data[0])):
        first_pos[pat + 1] = None
        for date in range(len(trace_data)):
            if trace_data[date][pat].endswith(".5"):
                first_pos[pat + 1] = date
                break
    return first_pos


def compute_epi_distance(pid1, pid2, trace_data, first_pos1, first_pos2, patient_ids):
    """
        Computes the epidemiological distance between two patients.

        Arguments:
        pid1 -- the assumed donor's index in trace data
        pid2 -- the assumed recipient's index in trace data
        trace_data -- data for days of overlap and first positive cultures
        first_pos1 -- the first positive test day for pid1
        first_pos2 -- the first positive test day for pid2
        patient_ids -- an ordered list of the patient IDs given in the text file

        Returns:
        Finds the epidemiological distance from patient 1 to
        patient 2.
        """
    first_overlap = -1
    assumed_trans_date = -1
    pid1 = patient_ids.index(pid1)
    pid2 = patient_ids.index(pid2)
    # Find the first overlap of the two patients
    for day in range(len(trace_data)):
        if (trace_data[day][pid1] == trace_data[day][pid2]) & \
                (trace_data[day][pid1] != "0"):
            first_overlap = day
            break
    if (first_pos2 < first_overlap) | (first_overlap < 0):
        return len(trace_data) * 2 + 1
    # Find the assumed transmission date from patient 1 to patient 2
    for day in range(first_pos2, -1, -1):
        if (trace_data[day][pid1] == trace_data[day][pid2]) & \
                (trace_data[day][pid1] != "0"):
            assumed_trans_date = day
            break
    sc_recip = first_pos2 - assumed_trans_date

    if first_pos1 < assumed_trans_date:
        sc_donor = 0
    else:
        sc_donor = first_pos1 - assumed_trans_date
    return sc_donor + sc_recip


def compute_pairwise_epi_distances(trace_data, patient_ids):
    """
        Turns the patient trace data into a dictionary of pairwise
        epidemiological distances.

        Arguments:
        trace_data -- a list of strings with patient trace data
        patient_ids -- ordered list of patient IDs to expect

        Returns:
        A dictionary of dictionaries where edist[i][j] is the
        epidemiological distance between i and j.
        """
    edist = {}
    proc_data = []
    # Reformat the trace data
    for i in range(len(trace_data)):
        temp = trace_data[i].split()[::-1]
        proc_data.append(temp)
    # Find first positive test days and remove the indication from the data
    first_pos = find_first_positives(proc_data)
    for pid in first_pos:
        day = first_pos[pid]
        proc_data[day][pid - 1] = proc_data[day][pid - 1].replace(".5", "")
    # Find the epidemiological distance between the two patients and add it
    # to the graph
    for pid1 in patient_ids:
        edist[pid1] = {}
        for pid2 in patient_ids:
            if pid1 != pid2:
                epi_dist = compute_epi_distance(pid1, pid2, proc_data,
                                                first_pos[pid1], first_pos[pid2], patient_ids)
                edist[pid1][pid2] = epi_dist
    return edist



def computemaxE(filename):
    """
    a helper function that computes the maximum epidemiological distance from the given data

        Arguments:
        filename -- the input file containing the sequences

        Returns:
        A integer that is the maximum epidemiological distance from the given data
    """
    proc_data = []
    trace_data = []

    with open(filename) as f:
        for line in f:
            if len(line.strip()) > 5:
                trace_data.append(line.strip())

    for trace in trace_data:

        temp = trace.split()[::-1]
        proc_data.append(temp)

    return max(max(proc_data))


def compute_genetic_distance(String1,String2):
    """
        computes the Hamming distance between two dna strings

           Arguments:
           String1-a binary sequence representing the genetic data
           String2-a binary sequence representing the genetic data

           Returns:
           An integer that is the genetic distance between the two sequences
       """
    i = 0
    distance = 0

    while (i < len(String1)):
        if (String1[i] != String2[i]):
            distance += 1
        i += 1
    return distance




def construct_complete_weighted_digraph(sequences,traces):
    """
  this function reads the epidemiological and genetic data and computes the
              Sequences- a file containing the genetic data
              traces-a file containing the epidemilogical data

              Returns:
              graph- a complete weighted digraph representing the infection transmission, whose nodes are
               the patients and whose edge weights are based on the given equation, where a higher
                weight represents a lower chance of transmisson
    """
    seq = read_patient_sequences(sequences)
    epi_distances = read_patient_traces(traces)
    epi_max = int(computemaxE(traces))

    graph = {}
    for node in epi_distances:
        graph[node] = {}
        for child in epi_distances[node]:
            genetic_distance = compute_genetic_distance(seq[node-1][1], seq[child-1][1])
            weight = genetic_distance + ((999 * (epi_distances[node][child] / epi_max)) / 10**5)
            graph[node][child] = weight
    
    return graph



### testing the functions

# computemaxE

# this function will be tested only once as the value can be read from the text file
# but this function validates the manual search of the value

# if int(computemaxE("patient_traces.txt"))==8:
#     print("function computemaxE has passed the test!")
# else:
#     print("function computemaxE has failed the test!")

# # compute genetic distance

# test_string_1='00'
# test_string_2='11'
# test_string_3='01011111111'
# test_string_4='10111111111'
# test_string_5='000'
# test_string_6='000'

# if compute_genetic_distance(test_string_1,test_string_2)==2 and \
#         compute_genetic_distance(test_string_3,test_string_4)==3 and\
#         compute_genetic_distance(test_string_5,test_string_6)==0:
#     print("function compute_genetic_distance has passed the tests!")

# # tests for construct_complete_weighted_digraph were not made because it requires more text files however i computed tests on the graph building part

# epi= {0: {1: 2, 2: 2, 3: 2, 4: 0,5: 0}, 1: {0: 2,2: 2, 3: 2,4: 0,5: 2}, 2: {0: 1, 1: 2, 3: 2, 4: 0, 5: 0}, 3: {0: 1 ,1: 0, 2: 0, 4: 2, 5: 2}, 4: {0: 1, 1: 2, 2: 2, 3: 2,4: 0,5: 0}, 5: {0: 1, 1: 2, 2: 2, 3: 2,4: 0}}

# graph={}
# for nodes in epi:
#     graph[nodes] = {}
#     for child in epi[nodes]:
#         graph[nodes][child] = 10



# ## build the complete graph and check the uniqueness
# gr=construct_complete_weighted_digraph("patient_sequences.txt","patient_traces.txt")
# rgraph=reverse_digraph_representation(gr)
# print("reversed graph:",rgraph)

# ## build a transmission map rooted at Patient 1
# map,weight=infer_transmap("patient_sequences.txt", "patient_traces.txt",1)
# print("map:",map)
# print("weight:",weight)






