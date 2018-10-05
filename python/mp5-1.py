import sys
import aig

import queue as q
from aig import SearchNode


def construct_solution(final_search_node):
    """
    Constructs string containing solution in proper format from final search node

    :param final_search_node: Result of search
    :return: String containing solution
    """

    indexes = []
    costs = []

    path_length = len(final_search_node.path)
    for path_index in range(path_length):

        indexes.append(final_search_node.path[path_index])

        if not path_index == path_length - 1:
            costs.append(final_search_node.costs[path_index])

    result = "Best path found:"
    for index in indexes:
        result += " {0}".format(index)

    result += "; cost:"
    for cost_index in range(len(costs)):
        result += " {0}".format(costs[cost_index])
        if not cost_index == len(costs) - 1:
            result += " +"

    result += " = {0}".format(final_search_node.total_cost)

    return result


def execute_greedy_search(graph, heuristic_index):
    """
    Executes greedy search on given graph and prints out the results

    :param graph Graph to execute greedy search on
    :param heuristic_index Index of heuristic to use for greedy search
    """

    if heuristic_index < 0 or graph.heuristics_count <= heuristic_index:
        raise Exception("You must provide correct index of heuristic to choose!")

    node = SearchNode(graph.start_nodes[0], 0, None)
    heuristic = graph.heuristics[heuristic_index]

    queue = q.PriorityQueue()
    queue.put((heuristic[node.node_index], node))

    step_counter = 0
    open_list = [node.node_index]
    closed_list = []

    while not queue.empty():
        (heuristic_cost, node) = queue.get()

        print('Step {0}:'.format(step_counter))
        print(' * OPEN: {0}'.format(open_list))
        print(' * CLOSED: {0}'.format(closed_list))

        if node.node_index in graph.goal_nodes:
            print(' * TO EVALUATE: {0} - GOAL NODE'.format(node.node_index))
            print('')
            break

        print(' * TO EVALUATE: {0}'.format(node.node_index))
        print('')

        step_counter += 1

        open_list.remove(node.node_index)
        closed_list.append(node.node_index)

        for (next_node, cost) in graph.nodes[node.node_index].items():
            if next_node not in closed_list and next_node not in open_list:
                queue.put((heuristic[next_node], SearchNode(next_node, cost, node)))
                open_list.append(next_node)

    print(construct_solution(node))


def run_program():
    """
    Main function of the program
    """

    if not aig.are_parameters_valid():
        raise Exception("You must provide the name of input file as first argument!")

    if len(sys.argv) < 3:
        chosen_heuristic = 0
    else:
        chosen_heuristic = int(sys.argv[2])

    graph = aig.parse_input(sys.argv[1])
    execute_greedy_search(graph, chosen_heuristic)


run_program()