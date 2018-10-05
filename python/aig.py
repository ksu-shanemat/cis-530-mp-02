import sys
import re
import copy

from enum import Enum


class InputMode(Enum):
    """
    Enumeration representing possible types of incidence input
    """

    LIST = 1
    MATRIX = 2


class Graph:
    """
    Class representing simple directed graph
    """

    def __init__(self):
        self.nodes_count = 0
        self.heuristics_count = 0
        self.start_nodes = []
        self.goal_nodes = []

        self.nodes = []
        self.heuristics = []

    def get_printable_adjacency_list(self):
        """
        Creates string representation of this graph as a adjacency list

        :return: Adjacency list describing this graph
        """

        res = ""
        for index in range(self.nodes_count):
            res += "    {0}".format(index)
            for (key, value) in self.nodes[index].items():
                res += " -> {0} ({1})".format(key, value)
            res += " -> NULL\n"
        res += "\n"

        return res

    def get_printable_adjacency_matrix(self):
        """
        Creates string representation of this graph as a adjacency matrix

        :return: Adjacency matrix describing this graph
        """

        res = ""
        for row_index in range(self.nodes_count):
            res += "    "
            for column_index in range(self.nodes_count):
                if not column_index in self.nodes[row_index]:
                    res += "* "
                else:
                    res += "{0} ".format(self.nodes[row_index][column_index])
            res += "\n"
        res += "\n"

        return res

    def __str__(self):
        res = "\n"
        res += "Graph:\n\n"
        res += " * nodes: {0}\n".format(self.nodes_count)
        res += "\n"
        res += " * start nodes:\n"
        res += "    "
        for index in range(len(self.start_nodes)):
            res += "{0} ".format(self.start_nodes[index])
        res += "\n\n"
        res += " * goal nodes:\n"
        res += "    "
        for index in range(len(self.goal_nodes)):
            res += "{0} ".format(self.goal_nodes[index])
        res += "\n\n"
        res += " * adjacency list:\n"
        res += "{0}".format(self.get_printable_adjacency_list())
        res += " * adjacency matrix:\n"
        res += "{0}".format(self.get_printable_adjacency_matrix())
        res += " * heuristics:\n"
        for node_index in range(self.nodes_count):
            res += "    {0} - ".format(node_index)
            for heuristic_index in range(len(self.heuristics)):
                res += "{0} ".format(self.heuristics[heuristic_index][node_index])
            res += "\n"
        res += "\n"

        return res


class NodeLink:
    """
    Class representing one link between nodes
    """

    def __init__(self, node_index, cost):
        self.node_index = node_index
        self.cost = cost

    def __str__(self):
        return "-> ({0}) {1}".format(self.cost, self.node_index)


class SearchNode:
    """
    Class representing search state
    """

    def __init__(self, node_index, cost, prev_node):
        self.node_index = node_index
        self.total_cost = 0

        if prev_node is None:
            self.path = []
            self.costs = []
        else:
            self.path = copy.deepcopy(prev_node.path)
            self.costs = copy.deepcopy(prev_node.costs)
            self.costs.append(cost)

        self.path.append(node_index)

        for part_cost in self.costs:
            self.total_cost += part_cost

    def __lt__(self, other):
        return self.total_cost < other.total_cost


def are_parameters_valid():
    """
    Checks whether the user provided program with at least one argument

    :return: True in case arguments are valid, false otherwise
    """

    return len(sys.argv) > 1


def is_comment_line(line):
    """
    Checks whether line is a comment

    :param line: Line to be checked
    :return: True in case line is a comment, false otherwise
    """

    return line.startswith("|")


def marks_graph_incidence(line, graph):
    """
    Checks whether line contains information of graph incidence

    :param line: Line to be checked
    :param graph: Graph being constructed
    :return: True in case line contains information about incidence, false otherwise
    """

    return line.startswith("#") or line.startswith("*") \
           or (len(line.split()) == graph.nodes_count and len(line.split()) > 1)


def skip_comments(lines, index):
    """
    Skips any comments from specified index on returning the first non-comment line
    or terminating program in case no non-comment lines remain

    :param lines: Lines of input file
    :param index: Current index to lines collection
    :return: The index of first non-comment line from specified index on
    """

    while index < len(lines):

        line = lines[index]
        if not is_comment_line(line):
            break

        index += 1

    if index == len(lines):
        raise Exception("Control reached end of file without finding necessary content!")

    return index


def convert_to_number_list(line_parts):
    """
    Attempts to convert given list of string variables to number list

    :param line_parts: List of string variables to be converted
    :return: List of corresponding numbers
    """

    number_list = []
    for part in line_parts:
        if not part.isdigit():
            raise Exception("Invalid data found in line {0}".format(line_parts))
        else:
            number_list.append(int(part))

    return number_list


def extract_node_links(line):
    """
    Extracts all links from specified line for an adjacency list format

    :param line: Line to be parsed
    :return: Array of NodeLinks
    """

    node_links = []
    link_fragments = line.split(" - ")

    for fragment in link_fragments:
        if fragment == "!":
            break

        parts = fragment.split(".")
        node_links.append(NodeLink(int(parts[0]), int(parts[1])))

    return node_links


def check_node_line_type(line, node_type):
    """
    Checks whether given line has specified type

    :param line: Line to be checked
    :param node_type: Type to be filtered
    :return: True in case last element of the given line matches given pattern, false otherwise
    """

    parts = line.split()
    return len(parts) > 0 and parts[-1] == node_type


def parse_nodes_count(lines, index, graph):
    """
    Parses the number of nodes from input lines and sets graph accordingly

    :param lines: Lines to be parsed
    :param index: Current line index
    :param graph: Graph to be modified
    :return Index of next line which should get parsed
    """

    index = skip_comments(lines, index)

    nodes_count = int(lines[index].split()[0])
    graph.nodes_count = nodes_count

    graph.start_nodes.append(0)
    graph.goal_nodes.append(nodes_count - 1)

    graph.nodes = [{} for x in range(nodes_count)]
    graph.heuristics = []

    return index + 1


def parse_additional_info(lines, index, graph):
    """
    Parses additional base information about graph being parsed such as indexes of start
    and goal nodes and number of chosen heuristic

    :param lines: Collection of lines of input file
    :param index: Index of currently parsed line
    :param graph: Parsed graph to be constructed
    :return: Index of next line which should get parsed
    """

    lines_to_process = []

    index = skip_comments(lines, index)
    line = lines[index]

    while not marks_graph_incidence(line, graph):
        lines_to_process.append(line)
        index += 1

        index = skip_comments(lines, index)
        line = lines[index]

    start_nodes_checked = False
    goal_nodes_checked = False
    unprocessed_lines = []

    for line in lines_to_process:
        if check_node_line_type(line, "S"):
            string_numbers = line.split()[:-1]
            graph.start_nodes = convert_to_number_list(string_numbers)

            start_nodes_checked = True
            continue

        if check_node_line_type(line, "G"):
            string_numbers = line.split()[:-1]
            graph.goal_nodes = convert_to_number_list(string_numbers)

            goal_nodes_checked = True
            continue

        unprocessed_lines.append(line)

    if len(unprocessed_lines) == 3:

        graph.start_nodes = convert_to_number_list(unprocessed_lines[0].split())
        graph.goal_nodes = convert_to_number_list(unprocessed_lines[1].split())
        graph.heuristics_count = int(unprocessed_lines[2].split()[0])

    elif len(unprocessed_lines) == 2:

        if not start_nodes_checked:
            graph.goal_nodes = convert_to_number_list(unprocessed_lines[0].split())
            graph.heuristics_count = int(unprocessed_lines[1].split()[0])
        elif not goal_nodes_checked:
            graph.start_nodes = convert_to_number_list(unprocessed_lines[0].split())
            graph.heuristics_count = int(unprocessed_lines[1].split()[0])
        else:
            graph.goal_nodes = convert_to_number_list(unprocessed_lines[0].split())
            graph.start_nodes = convert_to_number_list(unprocessed_lines[1].split())

    elif len(unprocessed_lines) == 1:

        graph.heuristics_count = int(unprocessed_lines[0].split()[0])

    else:
        raise Exception("Incorrect number of optional base graph arguments!")

    return index


def parse_adjacency_list(lines, graph):
    """
    Parses out the adjacency list from given lines

    :param lines: Lines containing information about adjacency list
    :param graph: Graph being constructed
    """

    for index in range(len(lines)):

        node_links = extract_node_links(lines[index])

        for list_index in range(len(node_links)):
            link = node_links[list_index]
            graph.nodes[index][link.node_index] = link.cost


def parse_adjacency_matrix(lines, graph):
    """
    Parses out the adjacency matrix from given lines

    :param lines: Lines containing information about adjacency matrix
    :param graph: Graph being constructed
    """

    for row_index in range(len(lines)):

        line = lines[row_index]
        for column_index in range(len(lines)):

            token = line.split()[column_index]
            if token == "*" or not token.isdigit():
                continue

            cost = int(token)

            graph.nodes[row_index][column_index] = cost


def parse_graph_incidence(lines, index, graph):
    """
    Parses information about graph incidence (either list or matrix type)

    :param lines: Collection of lines of input file
    :param index: Index of currently parsed line
    :param graph: Parsed graph to be constructed
    :return: Index of next line which should get parsed
    """

    input_mode = InputMode.MATRIX
    lines_to_process = []

    index = skip_comments(lines, index)
    line = lines[index]

    if line.startswith("#") or not re.match('^[.!\-0-9* \t\n]+$', line):
        index += 1

        if line.startswith("#list"):
            input_mode = InputMode.LIST

    index = skip_comments(lines, index)
    line = lines[index]

    while len(lines_to_process) < graph.nodes_count:
        lines_to_process.append(line)
        index += 1

        index = skip_comments(lines, index)
        line = lines[index]

    if input_mode == InputMode.LIST:
        parse_adjacency_list(lines_to_process, graph)
    else:
        parse_adjacency_matrix(lines_to_process, graph)

    return index


def parse_heuristics(lines, index, graph):
    """
    Parses information about given heuristics

    :param lines: Collection of lines of input file
    :param index: Index of currently parsed line
    :param graph: Parsed graph to be constructed
    """

    line = lines[index]
    lines_to_process = []

    while len(lines_to_process) < graph.nodes_count:
        lines_to_process.append(line)
        index += 1

        if len(lines_to_process) == graph.nodes_count:
            break

        index = skip_comments(lines, index)
        line = lines[index]

    for row_index in range(len(lines_to_process)):

        parts = lines_to_process[row_index].split()

        for heuristic_index in range(len(parts)):
            if row_index == 0:
                graph.heuristics.append([])

            graph.heuristics[heuristic_index].append(int(parts[heuristic_index]))


def parse_graph(lines):
    """
    Attempts to parse graph encoded in given lines

    :param lines: Lines to parse graph from
    :return: Parsed graph
    """

    graph = Graph()

    index = parse_nodes_count(lines, 0, graph)
    index = parse_additional_info(lines, index, graph)
    index = parse_graph_incidence(lines, index, graph)
    parse_heuristics(lines, index, graph)

    return graph


def parse_input(file_path):
    """
    Parses specified input file into directed graph

    :param file_path: Path (simplified) to input .aig file
    :return: Parsed graph from specified input file
    """

    input_file = open(file_path, encoding="utf8")
    lines = [line.rstrip('\n') for line in input_file]

    graph = parse_graph(lines)

    return graph
