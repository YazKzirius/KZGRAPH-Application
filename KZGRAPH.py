#AQA A-LEVEL COMPUTER SCIENCE NEA COURSEWORK CODE
#KZGRAPH APPLICATION
#Import Important libraries
from tkinter import *
from tkinter import scrolledtext
from PIL import Image, ImageTk
from binarytree import build, Node
import math as mt
import cmath as cmt
import numpy as np
import scipy as spy
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import (FigureCanvasTkAgg)
from mpl_toolkits import mplot3d
from mpl_toolkits.mplot3d import Axes3D
import networkx as nx
from sympy import *
from sympy.abc import x, y, z
import random

#Create User Interface main features
window = Tk()
window.geometry('1440x1024')
window.configure(bg='gray8')
window.title('KZGRAPH')

#Important constants/variables
π = mt.pi; j = 1j; e = mt.e

#Important Mathematical/Scientific functions
def Sjn(x):
    return mt.sin(mt.radians(x))

def Cos(x):
    return mt.cos(mt.radians(x))

def Tan(x):
    return mt.tan(mt.radians(x))

def ASjn(x):
    return mt.degrees(mt.asin(x))
  
def ACos(x):
    return mt.degrees(mt.acos(x))
 
def ATan(x):
    return mt.degrees(mt.atan(x))

def Sec(x):
    return (1 / mt.cos(mt.radians(x)))

def CoSec(x):
    return (1 / mt.sin(mt.radians(x)))
            
def Cot(x):
    return (1 / mt.tan(mt.radians(x)))   

def Ln(x):
    return mt.log(x)

#Converts Imaginary expressions into the required information to be processed
#Converts |z-3-i| = 5 into a locus to be outputted onto a Graph
def Convert_Locus(z):
    z = str(z)
    z = z.replace('i', 'j')
    if '|' in z and '=' in z:
        z = z.replace('|','')
        z = z.replace('z','')
        z = z.split('=')
        if isinstance(eval(z[-1]), int) == True or isinstance(eval(z[-1]),float) == True:
            Complex_number = complex(eval(z[0]))
            Centre = (-1*Complex_number.real, -1*Complex_number.imag)
            radius = eval(z[-1])
            return [Centre, radius]
        elif isinstance(eval(z[-1]), complex) == True:
            Complex_number = complex(eval(z[0]))
            z2 = complex(eval(z[-1]))
            Point1 = (-1*Complex_number.real, -1*Complex_number.imag)
            Point2 =(-1*z2.real, -1*z2.imag)
            return [Point1, Point2]
        elif isinstance(eval(z[0]), int) == True or isinstance(eval(z[0]),float) == True:
            Complex_number = complex(eval(z[-1]))
            Centre = (-1*Complex_number.real, -1*Complex_number.imag)
            radius = eval(z[0])
            return [Centre, radius]
    else:
        return False
    
#This function manipulates 3D algebra by making z the subject of the eqauations
#So they can be plotted onto the x, y and z axis
def make_z_subject(plane):
    if 'z' in plane and '=' in plane:
        plane = plane.replace('=', '-1*')
        plane = eval(plane)
        all_expressions = list(plane.args)
        polynomials = [i for i in all_expressions if 'z**' in str(i)]
        if len(polynomials) == 0:
            z_coeff = plane.coeff(z,1)
            equation = eval(str(plane).replace(str(z_coeff)+'*z','')) * -1 / z_coeff
        else:
            powers = []
            for polynomial in polynomials:
                polynomial = str(polynomial)
                powers.append(int(polynomial[-1]))
            highest_power = max(powers)
            z_coeff = plane.coeff(z,highest_power)
            for expression in all_expressions:
                if 'z**'+str(highest_power) in str(expression):
                    equation = (((eval(str(plane).replace(str(expression), '')) *-1) / z_coeff)) ** (1/highest_power)
                    equation = str(equation).replace('**1.0', '*1')
                    equation = eval(equation)
        return simplify(equation)
    else:
        return False

#This Function manipulates arg(z) functions and makes y the subject of the equation:
def Create_argument_equation(locus):
    Locus = str(locus)
    if 'arg(z' in locus:
        Locus = Locus.replace('arg(z', '(')
        Locus = Locus.split('=')
        z = complex(eval(Locus[0]))
        point = (-1*z.real, -1*z.imag)
        angle = eval(Locus[-1].replace('j','i'))
        #Argument z is the rise/run of a complex number
        #However for complex number z = x+iy, arg(z) = arctan(y/x)
        rise = str(eval('y+'+str(z.imag)))
        run = str(eval('x+'+str(z.real)))
        equation1 = '('+rise+')' + '/' + '('+run+')'+' = '+str(np.tan(angle))
        equation2 = rise +' = '+ str(eval(run) * np.tan(angle))
        simplified = str(eval(run) * np.tan(angle) - eval(rise.replace('y','')))
        x_coef = eval(simplified).coeff(x,1)
        if 'e-' in str(x_coef):
            simplified = simplified.replace(str(x_coef), '0')
        return simplified, point
    else:
        return False
             
#Data Structures below
#Graph Data structure class
class Graph:
    def __init__(self, V, E):
        self.vertices = set(V)
        self.gmatrix = []
        self.gdict = dict()
        self.get_edges(E)
        self.isweighted()

    #Converts checks if all edges are in the E set and replaces characters
    #It does this so that it van be evaluated
    def get_edges(self, edges):
        New_Edges = []
        G_edges = []
        letters = [chr(i) for i in range(65,91)] + [chr(i) for i in range(97,123)]
        edges = edges.replace(' ', '')
        edges = edges.replace('),', ') ')
        for letter in letters:
            edges = edges.replace(letter, '"'+letter+'"')
        Edge_List = edges.split(' ')
        New_Edges = [eval(i) for i in Edge_List]
        for i in New_Edges:
            edge = []
            for j in range(len(i)):
                if j < 2:
                    edge.append(str(i[j]))
                else:
                    edge.append(round(float(i[j]),4))
            G_edges.append(tuple(edge))
        for i in G_edges:
                if len(i) == 2:
                    if (i[1], i[0]) not in G_edges:
                        G_edges.append((i[1], i[0]))
                elif len(i) == 3:
                    if (i[1], i[0], i[2]) not in G_edges:
                        G_edges.append((i[1], i[0], i[2]))
        self.edges = set(G_edges)

    #This subroutine checks if a graph is a weighted or not
    # It does this by seting the weighted attrubute to True or False      
    def isweighted(self):
        Unweighted_count = 0
        Weighted_count = 0
        for i in self.edges:
            if len(i) == 3:
                Weighted_count += 1
            elif len(i) == 2:
                Unweighted_count += 1
        if Unweighted_count == len(self.edges):
            self.weighted = False
        elif Weighted_count == len(self.edges):
            self.weighted = True

    #Represents a Graph in an Adjacency list      
    def AdjacencyList(self):
        G = nx.Graph()
        Vx = list(sorted(self.vertices))
        if self.weighted == True:
            G.add_nodes_from([str(i).replace(' ', '') for i in Vx])
            G.add_weighted_edges_from(self.edges)
            self.gdict = G.adj
        else:
            for x in Vx:
                List = set()
                for edge in self.edges:
                    x = x.replace(' ','')
                    if x in edge:
                        if edge.index(x) != 1:
                            List.add(edge[-1])
                        else:
                            List.add(edge[0])
                self.gdict.update({x : sorted(list(List))})
        
    #Represents Graph in an Adjacency List
    def AdjacencyMatrix(self):
        G = nx.Graph()
        Vx = list(sorted(self.vertices))
        Vy = list(sorted(self.vertices))
        E0 = list(sorted(self.edges))
        if self.weighted == False:
            for x in range(len(Vx)):
                Matrix = []
                for y in range(len(Vy)):
                    if (Vx[x].replace(' ', ''),Vy[y].replace(' ', '')) in self.edges:
                        Matrix.append(1)
                    else:
                        Matrix.append(0)
                self.gmatrix.append(Matrix)
        else:
            Vx = [i.replace(' ','') for i in Vx]
            G.add_nodes_from(Vx)
            G.add_weighted_edges_from(E0)
            self.gmatrix = nx.to_numpy_matrix(G, nodelist=Vx)
            self.gmatrix = nx.to_numpy_array(G,nodelist=Vx)

    #Function performs Depth-first search algorithm on a graph using an Adjacency List
    def DFS(self):
        self.AdjacencyList()
        Vx = sorted(list(self.vertices))
        Traversals = []
        for node in Vx:
            node = node.replace(' ', '')
            visited = []
            stack = [node]
            while stack:
                vertex = stack.pop(-1)
                if vertex not in visited:
                    visited.append(vertex)
                    if self.weighted == False:
                        stack.extend(reversed(self.gdict[vertex]))
                    else:
                        stack.extend(reversed(sorted(list(self.gdict[vertex].keys()))))
            Traversals.append(visited)
        return Traversals
        
    #Function performs Breadth-first search algorithm on a graph using an Adjacency list
    def BFS(self):
        self.AdjacencyList()
        Vx = sorted(list(self.vertices))
        Traversals = []
        for node in Vx:
            node = node.replace(' ', '')
            visited = []
            queue = [node]
            while queue:
                vertex = queue.pop(0)
                if vertex not in visited:
                    visited.append(vertex)
                    if self.weighted == False:
                        neighbours = self.gdict[vertex]
                    else:
                        neighbours = sorted(list(self.gdict[vertex].keys()))
                    for neighbour in neighbours:
                        queue.append(neighbour)
            Traversals.append(visited)
        return Traversals

    #This function performs Djiksta's algorithm on a graph based on the weighted edges
    #by using an adjacency matrix
    def Djikstra(self, node):
        self.AdjacencyMatrix()
        if self.weighted == True:
            distances = [1e7] * len(self.gmatrix)
            distances[node] = 0
            shortest = [False] * len(self.gmatrix)
            for i in range(len(self.gmatrix)):
                min = 1e7
                matrix = self.gmatrix[node]
                for j in range(len(matrix)):
                    if distances[j] < min and shortest[j] == False:
                        min = distances[j]
                        min_index = j
                shortest[min_index] = True
                for j in range(len(matrix)):
                    if self.gmatrix[min_index][j] > 0 and \
                       shortest[j] == False and \
                       distances[j] > distances[min_index] + self.gmatrix[min_index][j]:
                        distances[j] = distances[min_index] + self.gmatrix[min_index][j]
            return distances
            
    #Outputs the possible shape of the graph onto matplotlib
    def DrawGraph(self):
        Vx = [i.replace(' ', '') for i in sorted(list(self.vertices))]
        G = nx.Graph()
        G.add_nodes_from(Vx)
        if self.weighted == True:
            G.add_weighted_edges_from(self.edges)
            pos=nx.spring_layout(G)
            nx.draw(G, pos, with_labels=True, font_weight='bold')
            edge_weight = nx.get_edge_attributes(G,'weight')
            nx.draw_networkx_edge_labels(G, pos, edge_labels = edge_weight)
        else:
            G.add_edges_from(self.edges)
            nx.draw(G, with_labels=True, font_weight='bold')

#Binary Tree Data structure class
class Binary_Tree:
    def __init__(self, node):
        self.left = None
        self.right = None
        self.left_nodes = []
        self.right_nodes = []
        self.item = node
        
    #Insert node into tree
    def insert_node(self, data):
        if self.item:
            if data < self.item:
                if self.left is None:
                    self.left = Binary_Tree(data)
                else:
                    self.left.insert_node(data)
                self.left_nodes.append(data)
            elif data > self.item:
                if self.right is None:
                    self.right = Binary_Tree(data)
                else:
                    self.right.insert_node(data)
                self.right_nodes.append(data)
        else:
            self.item = data

    #In-order traversal algorithm
    def inorder(self, n):
        Traversal = []
        if n:
            Traversal = self.inorder(n.left)
            Traversal = self.inorder(n.left)
            Traversal.append(n.item)
            Traversal += self.inorder(n.right)
        return Traversal

    #Pre-order traversal algorithm
    def preorder(self, n):
        Traversal = []
        if n:
            Traversal.append(n.item)
            Traversal += self.preorder(n.left)
            Traversal += self.preorder(n.right)
        return Traversal


    #Post-order traversal algorithm
    def postorder(self, n):
        Traversal = []
        if n:
            Traversal = self.postorder(n.left)
            Traversal += self.postorder(n.right)
            Traversal.append(n.item)
        return Traversal

#Stack Data structure class
class Stack:
    def __init__(self, expression):
        self.top = -1
        self.capacity = len(expression)
        self.contents = []
        self.output = []
        self.order_of_operations = {'+':3,
                                    '-':3,
                                    '*':2,
                                    '/':2,
                                    '^':1}

    #Checking is the stack is empty
    def IsEmpty(self):
        if self.top == -1:
            return True
        else:
            return False

    #Output the value at the top of the stack
    def peek(self):
        return self.contents[-1]

    #Pop an element from the stack
    def pop(self):
        if self.IsEmpty() == False:
            self.top -= 1
            return self.contents.pop()
        else:
            return 'Stack is Empty []'

    #Push an element onto the stack
    def push(self, item):
        self.top += 1
        self.contents.append(item)

    #Check is a function is a mathematical (operand) or quantity
    def IsOperand(self, operator):
        return operator.isalpha()

    #Checks order of operations to see if the program is
    #following the bidmas/bodmas operation orders
    def notGreater(self, index):
        try:
            n1 = self.order_of_operations[index]
            n2 = self.order_of_operations[self.peek()]
            if n1 <=n2:
                return True
            else:
                return False
        except KeyError:
            return False
        
    #Converting infix notation to postfix notation by pushing numbers onto the stack 
    #When an operator is spotted it will pop the previous element off the stack.
    def Convert_to_postfix(self, expression):
        for i in expression:
            if self.IsOperand(i):
                self.output.append(i)
            elif i == '(':
                self.push(i)
            elif i == ')':
                while self.IsEmpty() == False and self.peek() != '(':
                    a = self.pop()
                    self.output.append(a)
                if self.IsEmpty() == False and self.peek() != '(':
                    return -1
                else:
                    self.pop()
            else:
                while self.IsEmpty() == False and self.notGreater(i) == True:
                    self.output.append(self.pop())
                self.push(i)
        while self.IsEmpty() == False:
            self.output.append(self.pop())
        return ''.join(self.output)
	
    
#1. Create an Application Home page which contains two buttons, Get Started and How to use?
def default_home():
    global frame0
    frame0 = Frame(window, width = 1600, height = 1600, bg = 'gray8')
    frame0.place(x=0, y=0)
    GetStartedBtn = Button(frame0, text = 'Get Started', command = lambda: UserInterface(window),
                           font=('Helvetica 20',16), height=1, width=10, fg='white',
                           bg = 'black')
    GetStartedBtn.place(x=570, y=350)
    How_to_use_btn = Button(frame0, text = 'How to use?', font=('Helvetica 20',16),
                            height=1, width=10, fg='white', bg='black')
    How_to_use_btn.place(x=570, y=425)
    logo = Label(window, text = 'KZGRAPH', fg ='yellow', bg='gray8')    
    logo.config(font=('Comic Sans Ms',75))
    logo.place(x=400, y=150)
#Create a UserInterface class
#2. Create a Toggle Menu which allows efficient frame switching using a hamburger menu and a Close icon
class UserInterface:
    def __init__(self, window):
        self.window = window
        self.default_standard_calculator()
        #Open the two toggling images, the hamburger icon and the close icon
        self.Open = ImageTk.PhotoImage(Image.open("open.png").resize((50,50), Image.LANCZOS))
        self.Close = ImageTk.PhotoImage(Image.open("close.png").resize((50,50), Image.LANCZOS))
        #Create the hamburger button and set it as a global variable which can be acessed throughout the program
        global HamburgerButton
        HamburgerButton = Button(self.window, image=self.Open, command = self.toggle_window,
                                 border=0, bg = 'gray8', activebackground='gray8')
        HamburgerButton.place(x=1180, y=8)
        OptionsLabel = Label(self.window, text='Options',fg='white', bg='gray8')
        OptionsLabel.config(font=('Comic Sans Ms', 18))
        OptionsLabel.place(x=1080, y=10)
        
    #Create the Standard mode window frame UI which will display the Calculator features
    #by Instantiating the Standard_calculator class
    def default_standard_calculator(self):
        frame0.destroy()
        frame1 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame1.place(x=0,y=0)
        label1 = Label(frame1, text ='Standard Calculator', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=500, y=-10)
        logo = Label(frame1, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=600, y=300)
        Standard_Calculator()

    def Display_Standard_Calculator(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame1 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame1.place(x=0,y=0)
        label1 = Label(frame1, text ='Standard Calculator', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=500, y=-10)
        logo = Label(frame1, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=600, y=300)
        Standard_Calculator()
        self.toggle_window()

    #Create the Scientific mode window frame
    def Display_Scientific_Calculator(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame2 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame2.place(x=0,y=0)
        label1 = Label(frame2, text ='Scientific Calculator', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=500, y=-10)
        logo = Label(frame2, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=600, y=300)
        Scientific_Calculator()
        self.toggle_window()
        
    #Create the Graphical mode window frame
    def Display_Graphical_Calculator(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame3 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame3.place(x=0,y=0)
        label1 = Label(frame3, text ='Graphing Calculator', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=400, y=-10)
        function = Label(frame3, text='ƒ(x):', fg ='yellow', bg='gray8')
        function.config(font=('Comic Sans MS', 18))
        function.place(x=0, y=37)
        logo = Label(frame3, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=700, y=-10)
        Graphical_Calculator()
        Graphical_Calculator().Display_Grid()
        self.toggle_window()
        

    #Create a Imaginary Axis window frame
    def Display_Imaginary(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame4 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame4.place(x=0,y=0)
        label1 = Label(frame4, text ='The Imaginary Axis', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=500, y=-10)
        logo = Label(frame4, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=750, y=-10)
        CF1 = Label(frame4, text='Z:', fg ='yellow', bg='gray8')
        CF1.config(font=('Comic Sans MS', 18))
        CF1.place(x=0, y=37)
        Imaginary_Axis()
        Imaginary_Axis().Display_Imaginary_Grid()
        self.toggle_window()

    #Create a 3D Graphics window frame
    def Display_Graphics3D(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame5 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame5.place(x=0,y=0)
        label1 = Label(frame5, text ='Π:', fg ='yellow', bg ='gray8')
        label1.config(font=('Comic Sans Ms', 18))
        label1.place(x=0, y=37)
        label2 = Label(frame5, text ='3D Graphing', fg ='white', bg ='gray8')
        label2.config(font=('Comic Sans MS', 18))
        label2.place(x=500, y=-10)
        logo = Label(frame5, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=700, y=-10)
        Graphics3D()
        Graphics3D().Display_3D_Grid()
        self.toggle_window()
        
    #Create the Computational mode window frame 
    def Display_Computational_Calculator(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame6= Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame6.place(x=0,y=0)
        label1 = Label(frame6, text ='Computational Calculator', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=500, y=-10)
        logo = Label(frame6, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=600, y=300)
        Computational_Calculator()
        self.toggle_window()

    #Create the Graph theory window frame
    def Display_Graph_Theory(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame7 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame7.place(x=0, y=0)
        label1 = Label(frame7, text ='Graph Theory', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=400, y=-10)
        Vertices = Label(frame7, text='V:', fg ='yellow', bg='gray8')
        Vertices.config(font=('Comic Sans MS', 18))
        Vertices.place(x=0, y=37)
        Edges = Label(frame7, text ='E:', fg='yellow', bg='gray8')
        Edges.config(font=('Comic Sans MS',18))
        Edges.place(x=0, y=74)
        Output = Label(frame7, text ='Output:',fg='yellow', bg='gray8')
        Output.config(font=('Comic Sans MS',18))
        Output.place(x=0, y=555)
        logo = Label(frame7, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=700, y=-10)
        Graph_Theory_Calculator()
        self.toggle_window()

    #Display the Binary Tree calculator frame
    def Display_Binary_Tree_Calculator(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame8 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame8.place(x=0,y=0)
        label1 = Label(frame8, text ='Binary Tree Calculator', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=400, y=-10)
        Vertices = Label(frame8, text='V:', fg ='yellow', bg='gray8')
        Vertices.config(font=('Comic Sans MS', 18))
        Vertices.place(x=0, y=37)
        Output = Label(frame8, text ='Traversal:',fg='yellow', bg='gray8')
        Output.config(font=('Comic Sans MS',18))
        Output.place(x=0, y=520)
        Tree = Label(frame8, text ='Tree:',fg='yellow', bg='gray8')
        Tree.config(font=('Comic Sans MS',18))
        Tree.place(x=300, y=250)
        logo = Label(frame8, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=700, y=-10)
        Binary_Tree_Calculator()
        self.toggle_window()

    #Create the Reverse Polish Notation calculator frame
    def Display_RPN_Calculator(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame9 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame9.place(x=0, y=0)
        label1 = Label(frame9, text ='Reverse Polish Notation', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=500, y=-10)
        Infix = Label(frame9, text ='Expression:', fg ='white', bg ='gray8')
        Infix.config(font=('Comic Sans MS', 18))
        Infix.place(x=0, y=90)
        Postfix = Label(frame9, text ='RPN expression:', fg ='white', bg ='gray8')
        Postfix.config(font=('Comic Sans MS', 18))
        Postfix.place(x=0, y=214)
        logo = Label(frame9, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=665, y=400)
        RPN_Calculator()
        self.toggle_window()

    #Displays the Encryption Calculator frame
    def Display_Encryption_Calculator(self):
        self.Destroy_elements()
        ToggleFrame.destroy()
        frame10 = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        frame10.place(x=0,y=0)
        label1 = Label(frame10, text ='Encryption Calculator', fg ='white', bg ='gray8')
        label1.config(font=('Comic Sans MS', 18))
        label1.place(x=500, y=-10)
        Plaintext = Label(frame10, text ='Plain text:', fg ='white', bg ='gray8')
        Plaintext.config(font=('Comic Sans MS', 18))
        Plaintext.place(x=0, y=90)
        Shift = Label(frame10, text ='Shift:', fg ='white', bg ='gray8')
        Shift.config(font=('Comic Sans MS', 18))
        Shift.place(x=0, y=214)
        Key = Label(frame10, text ='Key:', fg ='white', bg ='gray8')
        Key.config(font=('Comic Sans MS', 18))
        Key.place(x=260, y=214)
        Ciphertext = Label(frame10, text ='Cipher text:', fg ='white', bg ='gray8')
        Ciphertext.config(font=('Comic Sans MS', 18))
        Ciphertext.place(x=0, y=338)
        logo = Label(frame10, text = 'KZGRAPH', fg = 'yellow', bg = 'gray8')
        logo.config(font=('Comic Sans MS',50))
        logo.place(x=665, y=420)
        Encryption_Calculator()
        self.toggle_window()

    def Quit_Program(self):
        self.window.destroy()

    #Destroys all elements of other application features:
    def Destroy_elements(self):
        self.Destroy_2DGrid()
        self.Destroy_IGrid()
        self.Destroy_3DGrid()
        self.Destroy_Graph()
        self.Destroy_Igraph()
        self.Destroy_GraphDS()
        self.Destroy_3DGraph()

    #Destroys the graph on the graphical calculator
    def Destroy_Graph(self):
        try:
            graph.destroy()
        except NameError:
            pass

    #Destroys the graph on the Graph theory calculator
    def Destroy_GraphDS(self):
        try:
            graph_ds.destroy()
        except NameError:
            pass

    #Destroys the graph on the imaginary axis calculator
    def Destroy_Igraph(self):
        try:
            I_graph.destroy()
        except NameError:
            pass

    #Destroys the graph on the 3D graphics calculator
    def Destroy_3DGraph(self):
        try:
            graph_3D.destroy()
        except NameError:
            pass

    #Destroys the individual 3D grid on the 3D graphics Calculator
    def Destroy_3DGrid(self):
        try:
            grid_3D.pack_forget()
        except NameError:
            pass
        
    #Destroys 2D grids in the graphical calculator
    def Destroy_2DGrid(self):
        try:
            grid.pack_forget()
        except NameError:
            pass

    #Destroys 2D grids in the imaginary calculator
    def Destroy_IGrid(self):
        try:
            I_grid.pack_forget()
        except NameError:
            pass

    #Create the menu toggle function which will allow the users to switch between calculator features or modes
    def toggle_window(self):
        global ToggleFrame
        ToggleFrame = Frame(self.window, width = 1440, height = 1024, bg = 'gray8')
        ToggleFrame.place(x=0, y=0)

        #Create the Menu toggle buttons
        def create_menu_button(x,y,text,bcolour,fcolour,command):

            #These functions handle key press events so when I clicked these buttons
            #it will display the frames
            def on_enter(event):
                myButton1['background'] = bcolour
                myButton1['foreground']= 'white'  

            def on_leave(event):
                myButton1['background'] = bcolour
                myButton1['foreground']= 'white'

            myButton1 = Button(ToggleFrame,text=text,
                               font = ('Helvetica 20',16),
                           width=20,
                           height=1,
                           fg='white',
                           border=0,
                           bg=bcolour,
                           activeforeground='white',
                           activebackground=bcolour,            
                            command=command)
                          
            myButton1.bind("<Enter>", on_enter)
            myButton1.bind("<Leave>", on_leave)
            myButton1.place(x=x,y=y)

        #Call the function to create the buttons which will appear under the hamburger icon
        create_menu_button(1000,80, 'Home', 'black', 'white', default_home)
        create_menu_button(1000,117,'Standard Calculator','black','white',self.Display_Standard_Calculator)
        create_menu_button(1000,154,'Scientific Calculator', 'black', 'white', self.Display_Scientific_Calculator)
        create_menu_button(1000,191,'Graphical Calculator', 'black', 'white', self.Display_Graphical_Calculator)
        create_menu_button(1010,228,'= Imaginary Axis', 'black', 'white', self.Display_Imaginary)
        create_menu_button(1010,265,'= 3D Graphing', 'black', 'white', self.Display_Graphics3D)
        create_menu_button(1000,302,'Computational Calculator','black','white',self.Display_Computational_Calculator)
        create_menu_button(1010,339,'= Graph Theory','black','white',self.Display_Graph_Theory)
        create_menu_button(1010,376,'= Binary Tree','black','white',self.Display_Binary_Tree_Calculator)
        create_menu_button(1010,413,'Reverse Polish Notation','black','white',self.Display_RPN_Calculator)
        create_menu_button(1010,450,'Encryption', 'black','white',self.Display_Encryption_Calculator)
        create_menu_button(1000,487,'Exit','black','white',self.Quit_Program)

        #Create a function to close the menu toggle when the close icon is clicked
        def CloseToggle():
            ToggleFrame.destroy()
            HamburgerButton = Button(self.window, image = self.Open,
                                     command = self.toggle_window,
                                     border=0,
                                     bg = 'gray8',
                                     activebackground ='gray8')
            HamburgerButton.place(x=1180, y=8)
            OptionsLabel = Label(self.window, text='Options',fg='white', bg='gray8')
            OptionsLabel.config(font=('Comic Sans Ms', 18))
            OptionsLabel.place(x=1080, y=10)

        CloseButton = Button(ToggleFrame, image=self.Close,
                             border = 0,
                             command = CloseToggle,
                             bg = 'gray8',
                             activebackground ='gray8')
        CloseButton.place(x=1180, y=10)


#3. Create a Standard Calculator feature:
# - It should be able to perform all standard Calculations
# - In addition, add factorials and rounding
class Standard_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.equation = Entry(window, width = 20,
                              font=('Helvetica 20',16), bd=30,
                              bg = 'gray8', fg = 'white')
        self.equation.place(x=0, y=0)
        self.equation.focus_set()#Sets focus on the input text area
        self.max_length = 200
        self.Create_Standard_Buttons()

   
    #This function replaces x with * and the divide symbol with /
    def GetandReplaceButtons(self):
        self.expression = self.equation.get()
        self.newtext = self.expression.replace('÷','/')
        self.newtext = self.newtext.replace('×', '*')

    #Generate the standard Calculator Buttons
    def Create_Standard_Buttons(self):
        #ROW1 BUTTONS
        #7,8,9,÷,AC,DEL
        Button(self.window,text="7", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action('7')).place(x=0, y=85)
 
        Button(self.window,text="8", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(8)).place(x=50, y=85)
 
        Button(self.window,text="9", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(9)).place(x=100, y=85)

        Button(self.window,text="÷", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action('÷')).place(x=150, y=85)
 
        Button(self.window,text='AC', font=('Helvetica 20',10), width=5,height=3,
               fg="white", bg="black",
               command=lambda:self.clear()).place(x=200, y=85)
 
        Button(self.window,text='DEL', font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.DEL()).place(x=250, y=85)

        #ROW2 BUTTONS
        #4,5,6,×,(,)
        Button(self.window,text="4", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(4)).place(x=0, y=140)
 
        Button(self.window,text="5", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(5)).place(x=50, y=140)
 
        Button(self.window,text="6", font=('Helvetica 20',10),width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(6)).place(x=100, y=140)
 
        Button(self.window,text="×", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action('×')).place(x=150, y=140)

        Button(self.window,text="(", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action('(')).place(x=200, y=140)
 
        Button(self.window,text=")", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(')')).place(x=250, y=140)

        #ROW3 BUTTONS
        #1,2,3,-,√,x²
        Button(self.window,text="1", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(1)).place(x=0, y=195)
 
        Button(self.window,text="2", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(2)).place(x=50, y=195)
 
        Button(self.window,text="3", font=('Helvetica 20',10),width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(3)).place(x=100, y=195)
 
        Button(self.window,text="-", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action('-')).place(x=150, y=195)

        Button(self.window,text="√x", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.sqrt()).place(x=200, y=195)
 
        Button(self.window,text="x²", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.square()).place(x=250, y=195)

        #ROW4 BUTTONS
        #0,.,Rnd,+,!,=
        Button(self.window,text="0", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action(0)).place(x=0, y=250)
 
        Button(self.window,text=".", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action('.')).place(x=50, y=250)

        Button(self.window,text="Rnd", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.round()).place(x=100, y=250)

        Button(self.window,text="+", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.action('+')).place(x=150, y=250)

        Button(self.window, text ='!', font=('Helvetica 20',10), width=5, height=3,
               fg='white',bg='black',
               command = lambda: self.factorial()).place(x=200, y=250)
        
        Button(self.window,text="=", font=('Helvetica 20',10), width=5,height=3,
               fg="white",bg="black",
               command=lambda:self.execute()).place(x=250, y=250)
        self.window.bind('<Return>',lambda event: self.execute())

    #Add Functionality to each of the buttons
    def execute(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.equation.delete(0,END)
            self.equation.insert(0, self.value)
    
    def sqrt(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError):
            self.e.delete(0, END)
            self.e.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.sqrtval = mt.sqrt(self.value)
            self.equation.delete(0, END)
            self.equation.insert(0, self.sqrtval)

    def square(self):
        try:
            self.GetandReplaceButtons()
            self.value= eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError):
            self.equation.delete(0,END)
            self.equation.insert(0,'MATH - SYNTAX ERROR!')
        else:
            self.sqval=mt.pow(self.value,2)
            self.equation.delete(0,END)
            self.equation.insert(0,self.sqval)

    def round(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError):
            self.equation.delete(0,END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.rounded = round(self.value, 2)
            self.equation.delete(0, END)
            self.equation.insert(0, self.rounded)

    def factorial(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        if len(str(mt.factorial(self.value))) > 150:
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - MAX LENGTH EXCEEDED')
        else:
            self.factvalue = mt.factorial(self.value)
            self.equation.delete(0, END)
            self.equation.insert(0, self.factvalue)
 
    def clear(self):
        self.equation.delete(0,END)
 
    def DEL(self):
        self.expression = self.equation.get()
        self.expression = self.expression[0:-1]
        self.equation.delete(0,END)
        self.equation.insert(END,self.expression)
 
    def action(self,argi):
        self.equation.insert(END,argi)
            
#4. Create a Scientific Calculator feature:
# - It should be able to perform all scientific calculations.
# - In addition, add complex number handling
class Scientific_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.equation = Entry(window, width = 18,
                              font=('Helvetica 20',16), bd=30,
                              bg = 'gray8', fg = 'white')
        self.equation. place(x=0, y=0)
        self.equation.focus_set()#Sets focus on the input text area
        self.Create_Scientific_Buttons()

    #This function replaces x with * and the divide symbol with /
    def GetandReplaceButtons(self):
        try:
            Functions = ['asin(', 'acos(', 'atan(','sin(', 'cos(', 'tan(', 'cosec(', 'sec', 'cot(', 'ln(']
            self.expression = self.equation.get()
            self.newtext = self.expression.replace('÷','/')
            self.newtext = self.newtext.replace('^','**')
            self.newtext = self.newtext.replace('³', '**3')
            self.newtext = self.newtext.replace('²','**2')
            self.newtext = self.newtext.replace('×', '*')
            for f in Functions:
                self.newtext = self.newtext.replace(f, f.capitalize())
            if 'Sin(' not in self.expression or 'Asin(' not in self.expression or 'Sin(x)' not in self.expression or 'sin(x)' not in self.expression or 'sin(y)' not in self.expression:
                self.newtext = self.newtext.replace('i', 'j')
            self.newtext = self.newtext.replace('%', '/100')
            self.Convert_Algebraic_Letters()
            self.Convert_Functions()
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    def Create_Scientific_Buttons(self):
        #Row1 Buttons
        #∫x dy, Deg, Rad, 1/x, dx/dy
        Button(self.window, text = '∫x dy', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.integrate_with_y()).place(x=0, y=85)

        Button(self.window, text = 'Deg', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.Convert_to_degrees()).place(x=55, y=85)

        Button(self.window, text = 'Rad', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.Convert_to_radians()).place(x=110, y=85)

        Button(self.window, text = '1/x', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('1/')).place(x=165, y=85)

        Button(self.window, text = 'dx/dy', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.differentiate_with_y()).place(x=220, y=85)
        
        #Row2 Buttons
        #∫y dx, x, y, |x|, dy-dx
        Button(self.window, text = '∫y dx', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command=lambda: self.integrate_with_x()).place(x=0, y=128)

        Button(self.window, text = 'x', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command=lambda: self.action('x')).place(x=55, y=128)

        Button(self.window, text = 'y', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command=lambda: self.action('y')).place(x=110, y=128)

        Button(self.window, text = '|x|', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.absolute()).place(x=165, y=128)

        Button(self.window, text = 'dy/dx', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.differentiate_with_x()).place(x=220, y=128)
        
        #Row3 Buttons
        #pi, e, i, arg, conj
        Button(self.window, text = 'π', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('π')).place(x=0, y=171)

        Button(self.window, text ='e', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('e')).place(x=55, y=171)

        Button(self.window, text = 'i', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('i')).place(x=110, y=171)

        Button(self.window, text='Arg(z)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.argument()).place(x=165, y=171)

        Button(self.window, text='Conj(z)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.conj()).place(x=220, y=171)

        #Row4 Buttons
        #sin, cos, tan, log, ln
        Button(self.window, text = 'Sin(x)', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Sin(')).place(x=0, y=214)

        Button(self.window, text = 'Cos(x)', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cos(')).place(x=55, y=214)

        Button(self.window, text = 'Tan(x)', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Tan(')).place(x=110, y=214)

        Button(self.window, text = 'Log(x)', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg = 'black', command = lambda: self.log10()).place(x=165, y=214)

        Button(self.window, text = 'Ln(x)', font=('Helvetica 20',10), width=6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Ln(')).place(x=220, y=214)

        #Row5 Buttons
        #asin, acos, atan, logab, e^x
        Button(self.window, text='Asin(x)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Asin(')).place(x=0, y=257)

        Button(self.window, text='Acos(x)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Acos(')).place(x=55, y=257)

        Button(self.window, text='Atan(x)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Atan(')).place(x=110, y=257)

        Button(self.window, text='10ⁿ', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('10^')).place(x=165, y=257)

        Button(self.window, text='eⁿ', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('e^')).place(x=220, y=257)

        #Row6 Buttons
        #sec, cosec, cot, AC, DEL
        Button(self.window, text='Sec(x)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Sec(')).place(x=0, y=300)

        Button(self.window, text='Cosec(x)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Cosec(')).place(x=55, y=300)

        Button(self.window, text='Cot(x)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Cot(')).place(x=110, y=300)

        Button(self.window, text = 'AC', font=('Helvetica 20',10), width=6, height=2, fg = 'white',
               bg = 'black', command=lambda: self.clear()).place(x=165, y=300)

        Button(self.window, text = 'DEL', font=('Helvetica 20',10), width = 6, height=2, fg = 'white',
               bg = 'black', command=lambda: self.DEL()).place(x=220, y=300)

        #Row7 Buttons
        #x^3, x^2 x^n, (, )
        Button(self.window, text='x³', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('³')).place(x=0, y=343)

        Button(self.window, text='x²', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('²')).place(x=55, y=343)

        Button(self.window, text='xⁿ', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda:self.action('^')).place(x=110, y=343)

        Button(self.window, text='(', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('(')).place(x=165, y=343)

        Button(self.window, text=')', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action(')')).place(x=220, y=343)

        #Row8 Buttons
        #7,8,9,X,/
        Button(self.window, text='7', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('7')).place(x=0, y=386)

        Button(self.window, text='8', font=('Helvetica 20',10),width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('8')).place(x=55, y=386)

        Button(self.window, text='9', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('9')).place(x=110, y=386)

        Button(self.window, text='×', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('×')).place(x=165, y=386)

        Button(self.window, text='÷', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black',command= lambda: self.action('÷')).place(x=220, y=386)

        #Row9 Buttons
        #4,5,6,+,-
        Button(self.window, text='4', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('4')).place(x=0, y=429)

        Button(self.window, text='5', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('5')).place(x=55, y=429)

        Button(self.window, text='6', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('6')).place(x=110, y=429)

        Button(self.window, text='+', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('+')).place(x=165, y=429)

        Button(self.window, text='-', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('-')).place(x=220, y=429)

        #Row10 Buttons
        #1,2,3,!,%
        Button(self.window, text='1', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black',command=lambda: self.action('1')).place(x=0, y=472)

        Button(self.window, text='2', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black',command=lambda: self.action('2')).place(x=55, y=472)

        Button(self.window, text='3', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('3')).place(x=110, y=472)

        Button(self.window, text='x!', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.factorial()).place(x=165, y=472)

        Button(self.window, text='%', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command=lambda: self.action('%')).place(x=220, y=472)

        #Row11 Buttons
        #0,.,Rnd, sqrt, =
        Button(self.window, text='0', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('0')).place(x=0, y=472+43)

        Button(self.window, text='.', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('.')).place(x=55, y=472+43)

        Button(self.window, text='Rnd', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command =lambda: self.round()).place(x=110, y=472+43)

        Button(self.window, text='²√x', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.sqrt()).place(x=165, y=472+43)

        Button(self.window, text='=',font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda:self.execute()).place(x=220, y=472+43)

        self.window.bind('<Return>',lambda event: self.execute())

    #Add functionality to the buttons
    def action(self, argi):
        self.equation.insert(END,argi)

    def clear(self):
        self.equation.delete(0,END)
 
    def DEL(self):
        self.expression = self.equation.get()
        self.expression = self.expression[0:-1]
        self.equation.delete(0,END)
        self.equation.insert(END,self.expression)
        
    #Replaces 2x, 3x, 4x etc with proper operations
    def Convert_Algebraic_Letters(self):
        Symbols = ['π', 'y', 'x', 'e']
        self.newtext = self.newtext.replace('ππ', 'π**2')
        self.newtext = self.newtext.replace('yy', 'y**2')
        self.newtext = self.newtext.replace('xx', 'x**2')
        self.newtext = self.newtext.replace('ee', 'e**2')
        for i in Symbols:
            for j in Symbols:
                self.newtext = self.newtext.replace(i+j,i+'*'+j)
        try:
            for i in range(0,10):
                for j in Symbols:
                    self.newtext = self.newtext.replace(str(i)+j,str(i)+'*'+j)  
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    #Converts Trig expressions so that it can be evaluated properly
    def Convert_Functions(self):
        Symbols = ['π', 'e']
        Functions = ['Sjn(', 'Cos(', 'Tan(', 'Sec(', 'Cosec(', 'Cot(', 'Ln(', 'Log(', 'ASjn(', 'ACos(', 'Atan(']
        try:
            for i in range(0, 10):
                for j in Functions:
                    self.newtext = self.newtext.replace(str(i)+j,str(i)+'*'+j)
            for i in Symbols:
                for j in Functions:
                    self.newtext = self.newtext.replace(i+j,i+'*'+j)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')
            
    #Returns a value when the equals button is clicked
    def execute(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.equation.delete(0,END)
            self.equation.insert(0, self.ReplaceExpression(str(self.value)))

    #Rounds up numbers to 3 significant figures
    def round(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0,END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.rounded = round(self.value, 2)
            self.equation.delete(0, END)
            self.equation.insert(0, self.rounded)

    #Performs factorial operations on numbers 
    def factorial(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.factvalue = mt.factorial(self.value)
            self.equation.delete(0, END)
            self.equation.insert(0, self.factvalue)

    #Performs the square root operator on numbers
    def sqrt(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation .insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.sqrtval = cmt.sqrt(self.value)
            if self.sqrtval.imag == 0:
                self.sqrtval = self.sqrtval.real
            self.equation.delete(0, END)
            self.equation.insert(0, self.sqrtval)

    #Performs the Complex conjugate operator on imaginary numbers
    def conj(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.conjugate = complex(self.value).conjugate()
            self.equation.delete(0, END)
            self.equation.insert(0, self.conjugate)

    #Performs argument z operator on numbers
    def argument(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.complexnumber = complex(self.value)
            if self.complexnumber.imag > 0 and self.complexnumber.real > 0:
                self.argz = mt.atan(abs(self.complexnumber.imag) / abs(self.complexnumber.real))
            elif self.complexnumber.imag > 0 and self.complexnumber.real < 0:
                self.argz = π - mt.atan(abs(self.complexnumber.imag) / abs(self.complexnumber.real))
            elif self.complexnumber.imag < 0 and self.complexnumber.real < 0:
                self.argz = -(π - (mt.atan(abs(self.complexnumber.imag) / abs(self.complexnumber.real))))
            elif self.complexnumber.imag < 0 and self.complexnumber.real > 0:
                self.argz = - (mt.atan(abs(self.complexnumber.imag) / abs(self.complexnumber.real)))
            self.equation.delete(0, END)
            self.equation.insert(0, self.argz)

    #Returns the absolute value of numbers and modulus of imaginary numbers
    def absolute(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.answer = abs(self.value)
            self.equation.delete(0, END)
            self.equation.insert(0, self.answer)

    #Performs logarithm to the base 10 on numbers
    def log10(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
            self.answer = mt.log10(self.value)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.equation.delete(0, END)
            self.equation.insert(0, self.answer)

    #Converts angles in degrees to radians
    def Convert_to_radians(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.answer = mt.radians(self.value)
            self.equation.delete(0, END)
            self.equation.insert(0, self.answer)

    #Converts angles in radians to degrees
    def Convert_to_degrees(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.answer = mt.degrees(self.value)
            self.equation.delete(0, END)
            self.equation.insert(0, self.answer)   
            

    #Performs differentiation with respect to x or y on expressions and returns it
    def differentiate_with_x(self):
        try:
            self.ReplaceFunctions()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.diff = diff(self.value, x)
            self.equation.delete(0, END)
            self.equation.insert(0, self.ReplaceExpression(str(self.diff)))

    def differentiate_with_y(self):
        try:
            self.ReplaceFunctions()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.diff = diff(self.value, y)
            self.equation.delete(0, END)
            self.equation.insert(0, self.ReplaceExpression(str(self.diff)))

    #Performs Integration with respect to x or y on functions or expressions and returns it
    def integrate_with_x(self):
        try:
            self.ReplaceFunctions()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.integral = integrate(self.value,x)
            self.equation.delete(0, END)
            self.equation.insert(0, self.ReplaceExpression(str(self.integral)))

    def integrate_with_y(self):
        try:
            self.ReplaceFunctions()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.integral = integrate(self.value,y)
            self.equation.delete(0, END)
            self.equation.insert(0, self.ReplaceExpression(str(self.integral)))

    #Replaces functions so that it can be differentiated or integrated
    def ReplaceFunctions(self):
        Algebraic_Symbols = ['x','y']
        Upper_Functions = ['Sin(', 'Cos(', 'Tan(', 'Cosec(', 'Sec','Cot(', 'Ln(',]
        Lower_Functions = [i.lower() for i in Upper_Functions]
        try:
            self.expression = self.equation.get()
            self.newtext = self.expression.replace('^','**')
            self.newtext = self.newtext.replace('³', '**3')
            self.newtext = self.newtext.replace('²','**2')
            self.newtext = self.newtext.replace('%', '/100')
            self.newtext = self.newtext.replace('÷','/')
            self.newtext = self.newtext.replace('×', '*')
            #For the Lowercase functions
            for i in range(0,10):
                for j in Lower_Functions:
                    self.newtext = self.newtext.replace(str(i)+j, str(i)+'*'+j)
            for i in Algebraic_Symbols:
                for j in Lower_Functions:
                    self.newtext = self.newtext.replace(i+j,i+'*'+j)
            for i in range(0,10):
                for j in Upper_Functions:
                    self.newtext = self.newtext.replace(str(i)+j, str(i)+'*'+j)
            for i in Algebraic_Symbols:
                for j in Upper_Functions:
                    self.newtext = self.newtext.replace(i+j,i+'*'+j)
            self.newtext = self.newtext.replace('Sin(','sin(')
            self.newtext = self.newtext.replace('Cos(','cos(')
            self.newtext = self.newtext.replace('Tan(','tan(')
            self.newtext = self.newtext.replace('Sec(', '1/cos(')
            self.newtext = self.newtext.replace('Cosec(', '1/sin(')
            self.newtext = self.newtext.replace('Cot(', '1/tan(')
            self.newtext = self.newtext.replace('Ln(', 'log(')
            self.newtext = self.newtext.replace('Ln(','log(')
            self.Convert_Algebraic_Letters()
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')
            
    #Replaces operators in expressions so that it can make a function more readable for the user
    def ReplaceExpression(self, expression):
        Functions = ['sin(', 'cos(', 'tan(', 'Sec(', 'Cosec(', 'Cot(', 'Ln(',]
        expression = expression.replace('**2','²')
        expression = expression.replace('**3', '³')
        expression = expression.replace('**','^')
        expression = expression.replace('*x', 'x')
        expression = expression.replace('*y','y')
        for f in Functions:
            expression = expression.replace('*'+f,f)
        expression = expression.replace('log(','Ln(')
        expression = expression.replace('cos(x)/sin(x)','Cot(x)')
        expression = expression.replace('sin(x)/cos(x)','Tan(x)')
        expression = expression.replace('cos(y)/sin(y)','Cot(y)')
        expression = expression.replace('sin(y)/cos(y)','Tan(y)')
        expression = expression.replace('1/sin(x)','Cosec(x)')
        expression = expression.replace('1/cos(x)','Sec(x)')
        expression = expression.replace('1/sin(y)','Cosec(y)')
        expression = expression.replace('1/cos(y)','Sec(y)')
        return expression


#5. Create a Graphical Calculator feature:
# - It should be able to plot most graphical functions.
class Graphical_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.f1 = Entry(window, width=50, font=('Helvetica 20', 16),
                        bg = 'gray8', fg = 'white')
        self.f1.place(x=60,y=44)
        self.f1.focus_set()
        self.Create_Graphical_Buttons()

    #Display an Empty graph or grid before the execute button is pressed
    def Display_Grid(self):
        plt.style.use('dark_background')
        global Grid_figure, Grid_ax, grid
        Grid_figure = plt.figure(figsize=(9,7), dpi=100)
        Grid_ax = Grid_figure.add_subplot(1, 1, 1)
        Grid = FigureCanvasTkAgg(Grid_figure, self.window)
        grid = Grid.get_tk_widget()
        grid.pack(side=RIGHT)
        self.current_graph = grid
        Grid_ax.set_xlabel('x')
        Grid_ax.set_ylabel('y')
        self.Centre_Grid_Axis()
        plt.grid()

    def Centre_Grid_Axis(self):
        Grid_ax.spines['left'].set_position('center')
        Grid_ax.spines['bottom'].set_position('zero')
        Grid_ax.spines['right'].set_color('none')
        Grid_ax.spines['top'].set_color('none')
        Grid_ax.xaxis.set_ticks_position('bottom')
        Grid_ax.yaxis.set_ticks_position('left')

    #Replace Buttons with their specified function
    def GetandReplaceButtons(self):
        try:
            Lower_Functions = ['asin(', 'acos(', 'atan(', 'sin(', 'cos(', 'tan(', 'cosec(', 'sec(' 'cot(']
            self.expression = self.f1.get()
            self.newtext = self.expression.replace('×', '*')
            self.newtext = self.newtext.replace(' ', '')
            self.newtext = self.newtext.replace('%', '/100')
            self.newtext = self.newtext.replace('^','**')
            self.newtext = self.newtext.replace('³', '**3')
            self.newtext = self.newtext.replace('²','**2')
            self.newtext = self.newtext.replace('sqrt(', 'np.sqrt(')
            if self.newtext.find('y=') == 0:
                self.newtext = self.newtext.replace('y=', '')
            for lf in Lower_Functions:
                self.newtext = self.newtext.replace(lf, lf.capitalize())
            self.Convert_Functions()
            self.Convert_Algebraic_Letters()
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')
    
    #Create the Graphical Calculator Buttons
    def Create_Graphical_Buttons(self):
        #ROW1 BUTTONS
        #π, =, x, y, AC, DEL
        Button(self.window, text = 'π', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('π')).place(x=0,y=243)

        Button(self.window, text ='x', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('x')).place(x=55,y=243)

        Button(self.window, text ='y', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('y')).place(x=110,y=243)

        Button(self.window, text ='=', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('=')).place(x=165,y=243)
        
        Button(self.window, text ='AC', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.clear()).place(x=220,y=243)

        Button(self.window, text ='DEL', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.DEL()).place(x=275,y=243)
        
        #ROW2 BUTTONS
        #Sin, Cos, Tan, Log, Ln, log(a, b)
        Button(self.window, text ='Sin(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Sin(')).place(x=0,y=286)

        Button(self.window, text ='Cos(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cos(')).place(x=55,y=286)

        Button(self.window, text ='Tan(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Tan(')).place(x=110,y=286)

        Button(self.window, text ='Log(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Log(')).place(x=165,y=286)

        Button(self.window, text ='Ln(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Ln(')).place(x=220,y=286)

        Button(self.window, text =',', font = ('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(', ')).place(x=275,y=286)

        #ROW3 BUTTONS
        #Asin, Acos, Atan, e^x, |x| 
        Button(self.window, text ='Asin(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Asin(')).place(x=0,y=329)

        Button(self.window, text ='Acos(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Acos(')).place(x=55,y=329)

        Button(self.window, text ='Atan(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Atan(')).place(x=110,y=329)

        Button(self.window, text ='e', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('e')).place(x=165,y=329)

        Button(self.window, text ='eⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('e^')).place(x=220,y=329)

        Button(self.window, text ='|x|', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('abs(')).place(x=275,y=329)

        #ROW4 BUTTONS
        #Sec, Cosec, Cot, x^3, x^2, ,1/x
        Button(self.window, text ='Sec(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Sec(')).place(x=0,y=372)

        Button(self.window, text ='Cosec(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cosec(')).place(x=55,y=372)

        Button(self.window, text ='Cot(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cot(')).place(x=110,y=372)

        Button(self.window, text ='x³', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('³')).place(x=165,y=372)

        Button(self.window, text ='x²', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('²')).place(x=220,y=372)

        Button(self.window, text ='1/x', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('1/')).place(x=275,y=372)

        #ROW5 BUTTONS
        #(, ), 7, 8, 9, ×
        Button(self.window, text ='(', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('(')).place(x=0,y=415)

        Button(self.window, text =')', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(')')).place(x=55,y=415)

        Button(self.window, text ='7', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('7')).place(x=110,y=415)

        Button(self.window, text ='8', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('8')).place(x=165,y=415)

        Button(self.window, text ='9', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('9')).place(x=220,y=415)

        Button(self.window, text ='×', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('×')).place(x=275,y=415)

        #ROW6 BUTTONS
        #x^n, sqrt, 4, 5, 6, -
        Button(self.window, text ='xⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('^')).place(x=0,y=458)

        Button(self.window, text ='²√x', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('sqrt(')).place(x=55,y=458)

        Button(self.window, text ='4', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('4')).place(x=110,y=458)

        Button(self.window, text ='5', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('5')).place(x=165,y=458)

        Button(self.window, text ='6', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('6')).place(x=220,y=458)

        Button(self.window, text ='-', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('-')).place(x=275,y=458)

        #ROW7 BUTTONS
        #÷, %, 1, 2, 3, +
        Button(self.window, text ='÷', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('/')).place(x=0,y=501)

        Button(self.window, text ='%', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('%')).place(x=55,y=501)

        Button(self.window, text ='1', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('1')).place(x=110,y=501)

        Button(self.window, text ='2', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('2')).place(x=165,y=501)

        Button(self.window, text ='3', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('3')).place(x=220,y=501)

        Button(self.window, text ='+', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('+')).place(x=275,y=501)

        #ROW8 BUTTONS
        #10ⁿ, !, 0, ., exit, exe
        Button(self.window, text ='10ⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('10^')).place(x=0,y=544)

        Button(self.window, text ='.', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('.')).place(x=55,y=544)

        Button(self.window, text ='0', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('0')).place(x=110,y=544)

        Button(self.window, text ='Save', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.Save_Graph()).place(x=165,y=544)

        Button(self.window, text ='Exit', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.remove_plot(self.current_graph)).place(x=220,y=544)

        Button(self.window, text ='Exe', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.execute()).place(x=275,y=544)

        self.window.bind('<Return>',lambda event: self.execute())
        
    #Add functionality to the buttons
    def action(self, argi):
        self.f1.insert(END, argi)

    def clear(self):
        self.f1.delete(0,END)
 
    def DEL(self):
        self.expression = self.f1.get()
        self.expression = self.expression[0:-1]
        self.f1.delete(0,END)
        self.f1.insert(END,self.expression)

    #Replaces Trigonometric and Logarithmic functions with the necessary operators
    def Convert_Functions(self):
        Functions = ['Sin(', 'Cos(', 'Tan(', 'Cosec(', 'sec', 'Cot(', 'Log(', 'Ln(', 'Asin(', 'Acos(', 'Atan(']
        Symbols = ['x', 'y', 'π', 'e']
        try:
            self.newtext = self.newtext.replace('ASin(', 'Asin(')
            self.newtext = self.newtext.replace('ACos(', 'Acos(')
            self.newtext = self.newtext.replace('ATan(', 'Atan(')
            for i in range(0, 10):
                for j in Functions:
                    self.newtext = self.newtext.replace(str(i)+j, str(i)+'*'+j)
            for i in Symbols:
                for j in Functions:
                    self.newtext = self.newtext.replace(i+j, i+'*'+j)
            self.newtext = self.newtext.replace('Sin(','np.sin(')
            self.newtext = self.newtext.replace('Cos(','np.cos(')
            self.newtext = self.newtext.replace('Tan(','np.tan(')
            self.newtext = self.newtext.replace('Cosec(','1/np.sin(')
            self.newtext = self.newtext.replace('Sec(','1/np.cos(')
            self.newtext = self.newtext.replace('Cot(','1/np.tan(')
            self.newtext = self.newtext.replace('Log(','np.log(')
            self.newtext = self.newtext.replace('Ln(','np.log10(')
            self.newtext = self.newtext.replace('Asin(','np.arcsin(')
            self.newtext = self.newtext.replace('Acos(','np.arccos(')
            self.newtext = self.newtext.replace('Atan(','np.arctan(')   
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    #Converts Algebraic letters so that they can be evaluated and outputted in a graph
    def Convert_Algebraic_Letters(self):
        Symbols = ['x', 'y', 'z', 'π', 'e']
        try:
            self.newtext = self.newtext.replace('ππ', 'π**2')
            self.newtext = self.newtext.replace('yy', 'y**2')
            self.newtext = self.newtext.replace('xx', 'x**2')
            self.newtext = self.newtext.replace('zz', 'z**2')
            self.newtext = self.newtext.replace('ee', 'e**2')
            for i in range(0, 10):
                for j in Symbols:
                    self.newtext = self.newtext.replace(str(i)+j, str(i)+'*'+j)
            for i in Symbols:
                for j in Symbols:
                    self.newtext = self.newtext.replace(i+j, i+'*'+j)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    #Removes Plot on the screen and allows the user to plot another graph
    def remove_plot(self, graph):
        graph.pack_forget()

    #Allows the user to save their Graph as a png file
    def Save_Graph(self):
        plt.savefig(str(self.expression)+'.png')

    #Replaces Curves with necessary operators so users can understand what the plot is
    def Replace_Labels(self):
        self.expression = self.expression.replace('asin', 'arcsin(')
        self.expression = self.expression.replace('Asin(', 'arcsin(')
        self.expression = self.expression.replace('acos', 'arccos(')
        self.expression = self.expression.replace('Acos(', 'arccos(')
        self.expression = self.expression.replace('atan', 'arctan(')
        self.expression = self.expression.replace('Atan(', 'arctan(')
        self.expression = self.expression.replace('x^2', 'x²')
        self.expression = self.expression.replace('x^3', 'x³')

    #Centres the y and x axis including a negative axis
    def Centre_Graph_Axis(self):
        ax.spines['left'].set_position('center')
        ax.spines['bottom'].set_position('zero')
        ax.spines['right'].set_color('none')
        ax.spines['top'].set_color('none')
        ax.xaxis.set_ticks_position('bottom')
        ax.yaxis.set_ticks_position('left')
        
    #Plots a graph based on the data entered into the f1 entry box
    def execute(self):
        plt.style.use('dark_background')
        try:
            self.GetandReplaceButtons()
            self.remove_plot(self.current_graph)
            global figure, ax, graph
            figure = plt.figure(figsize=(9,7), dpi=100)
            ax = figure.add_subplot(1, 1, 1)
            Graph = FigureCanvasTkAgg(figure, self.window)
            graph = Graph.get_tk_widget()
            graph.pack(side=RIGHT)
            self.current_graph = graph
            self.functions = self.newtext.split(',')
            line_colours = ['y', 'b', 'r', 'g', 'c', 'm', 'w']
            for i in range(len(self.functions)):
                if 'np.sin(' in self.functions[i] or 'np.cos(' in self.functions[i] or'np.tan(' in self.functions[i]:
                    x = np.linspace(-20, 20, 100)
                    y = np.linspace(-20,20,100)
                    self.function = eval(self.functions[i])
                    self.Centre_Graph_Axis()
                    self.Replace_Labels()
                    plt.plot(x,self.function, line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i]))
                    plt.legend(loc='upper left')
                        
                elif 'np.log(' in self.functions[i] or 'np.log10(' in self.functions[i]:
                    x = np.linspace(-20,20, 100)
                    y =  np.linspace(-10,10,100)
                    self.function = eval(self.functions[i])
                    self.Replace_Labels()
                    plt.plot(x,self.function, line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i]))
                    plt.legend(loc='upper left')
                        
                elif 'x' in self.functions[i] and 'y' in self.functions[i] and '=' in self.functions[i]:
                    X = np.linspace(-20.0, 20.0, 100)
                    Y = np.linspace(-20.0, 20.0, 100)
                    x, y = np.meshgrid(X,Y)
                    self.newtext = self.functions[i].replace('=','-1*')
                    self.function = eval(self.newtext)
                    self.Centre_Graph_Axis()
                    Contour = ax.contour(x,y,self.function, [0], colors=line_colours[i])
                    
                elif 'x=' in self.functions[i]:
                    x = np.linspace(-20,20, 100)
                    y =  np.linspace(-20,20,100)
                    self.function = eval(self.functions[i].replace('x=', ''))
                    if self.function < 0:
                        self.Centre_Graph_Axis()
                        self.Replace_Labels()
                        plt.axvline(x = self.function, color=line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i]))
                    else:
                        self.Replace_Labels()
                        plt.axvline(x = self.function, color=line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i]))

                elif 'np.arc' in self.functions[i]:
                    x = np.linspace(-5,5, 100)
                    y =  np.linspace(-5,5,100)
                    self.function = eval(self.functions[i])
                    self.Centre_Graph_Axis()
                    self.Replace_Labels()
                    plt.plot(x, self.function, line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i])) 
                    
                else:
                    x = np.linspace(-20,20, 100)
                    y =  np.linspace(-20,20,100)
                    self.function = eval(self.functions[i])
                    if isinstance(self.function, int) == True or isinstance(self.function, float) == True:
                        if self.function < 0:
                            self.Centre_Graph_Axis()
                            self.Replace_Labels()
                            plt.axhline(y = self.function, color = line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i]))
                        else:
                            self.Replace_Labels()
                            plt.axhline(y = self.function, color = line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i]))
                    else:
                        self.Centre_Graph_Axis()
                        self.Replace_Labels()
                        plt.plot(x, self.function, line_colours[i], label = 'ƒ'+str(i+1)+': '+str(self.expression.split(',')[i]))
            plt.legend(loc='upper left')
            ax.set_xlabel('x')
            ax.set_ylabel('y')
            plt.grid()
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.f1.delete(0, END)
            self.f1.insert(0, 'MATH - SYNTAX ERROR')

#SUBTASK 1. Create a Imaginary Axis Feature
#- It should be able to plot complex numbers on an argand diagram and draw a locus.
class Imaginary_Axis(UserInterface):
    def __init__(self):
        self.window = window
        self.CF = Entry(window, width = 55, font=('Helvetica 20',16), bg = 'gray8', fg = 'white')
        self.CF.place(x=30, y=45)
        self.CF.focus_set()
        self.Create_Imaginary_Buttons()

    #Display an Empty Graph or grid before the execute button is pressed
    def Display_Imaginary_Grid(self):
        plt.style.use('dark_background')
        global I_Grid_figure, I_Grid_ax, I_grid
        I_Grid_figure = plt.figure(figsize=(9,7), dpi=100)
        I_Grid_ax = I_Grid_figure.add_subplot(1, 1, 1)
        Grid = FigureCanvasTkAgg(I_Grid_figure, self.window)
        I_grid = Grid.get_tk_widget()
        I_grid.pack(side=RIGHT)
        self.current_graph = I_grid
        I_Grid_ax.set_xlabel('Re(z)')
        I_Grid_ax.set_ylabel('Im(z)')
        self.Centre_Grid_Axis()
        plt.grid()

    def Centre_Grid_Axis(self):
        I_Grid_ax.spines['left'].set_position('center')
        I_Grid_ax.spines['bottom'].set_position('zero')
        I_Grid_ax.spines['right'].set_color('none')
        I_Grid_ax.spines['top'].set_color('none')
        I_Grid_ax.xaxis.set_ticks_position('bottom')
        I_Grid_ax.yaxis.set_ticks_position('left')
        
    #Replaces buttons and operators with their specified functions
    def GetandReplaceButtons(self):
        self.expression = self.CF.get()
        self.newtext = self.expression.replace('*', '.conjugate()')
        self.newtext = self.newtext.replace('×', '*')
        self.newtext = self.newtext.replace('^','**')
        self.newtext = self.newtext.replace('²','**2')
        self.newtext = self.newtext.replace('πi', 'π*i')
        self.newtext = self.newtext.replace('i', 'j')
        self.newtext = self.newtext.replace('z=', '')
        self.newtext = self.newtext.replace('sqrt(', 'cmt.sqrt(')
        self.Convert_Functions()
        
        
    #Create the Imaginary Axis Buttons
    def Create_Imaginary_Buttons(self):
        #ROW1 BUTTONS
        #π, comma, i, =, AC, DEL
        Button(self.window, text = 'π', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('π')).place(x=0,y=243)

        Button(self.window, text ='z', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('z')).place(x=55,y=243)

        Button(self.window, text ='i', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('i')).place(x=110,y=243)

        Button(self.window, text ='=', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('=')).place(x=165,y=243)
        
        Button(self.window, text ='AC', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.clear()).place(x=220,y=243)

        Button(self.window, text ='DEL', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.DEL()).place(x=275,y=243)

        #ROW2 BUTTONS
        #Sin, Cos, Tan, arg, conj, |z|
        Button(self.window, text ='Sin(x)', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Sin(')).place(x=0,y=286)

        Button(self.window, text ='Cos(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cos(')).place(x=55,y=286)

        Button(self.window, text ='Tan(x)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Tan(')).place(x=110,y=286)

        Button(self.window, text ='arg(z)', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('arg(')).place(x=165,y=286)
        
        Button(self.window, text ='|z|', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('|')).place(x=220,y=286)

        Button(self.window, text =',', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(', ')).place(x=275,y=286)

        #ROW3 BUTTONS
        #(, ), 7, 8, 9, X
        Button(self.window, text ='(', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('(')).place(x=0,y=329)

        Button(self.window, text =')', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(')')).place(x=55,y=329)

        Button(self.window, text ='7', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('7')).place(x=110,y=329)

        Button(self.window, text ='8', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('8')).place(x=165,y=329)
        
        Button(self.window, text ='9', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('9')).place(x=220,y=329)

        Button(self.window, text ='×', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('×')).place(x=275,y=329)
        

        #ROW4 BUTTONS
        #x^n, *, 4, 5, 6, -
        Button(self.window, text ='xⁿ', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('^')).place(x=0,y=372)

        Button(self.window, text ='*', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('*')).place(x=55,y=372)

        Button(self.window, text ='4', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('4')).place(x=110,y=372)

        Button(self.window, text ='5', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('5')).place(x=165,y=372)
        
        Button(self.window, text ='6', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('6')).place(x=220,y=372)

        Button(self.window, text ='-', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('-')).place(x=275,y=372)

        #ROW5 BUTTONS
        #²√x, ÷, 1, 2, 3, +
        Button(self.window, text ='²√x', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('sqrt(')).place(x=0,y=415)

        Button(self.window, text ='÷', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('/')).place(x=55,y=415)

        Button(self.window, text ='1', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('1')).place(x=110,y=415)

        Button(self.window, text ='2', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('2')).place(x=165,y=415)
        
        Button(self.window, text ='3', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('3')).place(x=220,y=415)

        Button(self.window, text ='+', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('+')).place(x=275,y=415)
        

        #ROW6 BUTTONS
        #x^2, .,0,  Save, Exit, Exe
        Button(self.window, text ='x²', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('²')).place(x=0,y=458)

        Button(self.window, text ='.', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('.')).place(x=55,y=458)

        Button(self.window, text ='0', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('0')).place(x=110,y=458)

        Button(self.window, text ='Save', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.Save_Graph()).place(x=165,y=458)
        
        Button(self.window, text ='Exit', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.remove_plot(self.current_graph)).place(x=220,y=458)

        Button(self.window, text ='Exe', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.execute()).place(x=275,y=458)

        self.window.bind('<Return>',lambda event: self.execute())

    #Add Functionality to buttons
    def action(self, argi):
        self.CF.insert(END, argi)

    def clear(self):
        self.CF.delete(0,END)
 
    def DEL(self):
        self.expression = self.CF.get()
        self.expression = self.expression[0:-1]
        self.CF.delete(0,END)
        self.CF.insert(END,self.expression)
        
    #Replace Trignometric functions with the necessary operators
    def Convert_Functions(self):
        Functions = ['Sin(', 'Cos(', 'Tan(', 'j']
        try:
            self.newtext = self.newtext.replace('πSin(', 'π*Sin(')
            self.newtext = self.newtext.replace('πCos(', 'π*Cos(')
            self.newtext = self.newtext.replace('πTan(', 'π*Tan(')
            self.newtext = self.newtext.replace('πj(', 'π*j')
            self.newtext = self.newtext.replace('jSin(', 'j*Sin(')
            self.newtext = self.newtext.replace('jCos(', 'j*Cos(')
            self.newtext = self.newtext.replace('jTan(', 'j*Tan(')
            for i in range(0, 10):
                for j in Functions:
                    self.newtext = self.newtext.replace(str(i)+j, str(i)+'*'+j)
            for i in range(0,10):
                self.newtext = self.newtext.replace(str(i)+'π',str(i)+'*π')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    #Removes Plot on the screen and allows the user to plot another graph
    def remove_plot(self, graph):
        graph.pack_forget()

    #Allows the user to save their Graph as a png file
    def Save_Graph(self):
        plt.savefig('Argand diagram.png')

    #This function centres the Im(z) and Re(z) axis
    def Centre_Graph_Axis(self):
        I_ax.spines['left'].set_position('center')
        I_ax.spines['bottom'].set_position('zero')
        I_ax.spines['right'].set_color('none')
        I_ax.spines['top'].set_color('none')
        I_ax.xaxis.set_ticks_position('bottom')
        I_ax.yaxis.set_ticks_position('left')
                                                              
    #Plot a graph based on the data entered into the CF entry box
    def execute(self):
        plt.style.use('dark_background')
        self.remove_plot(self.current_graph)
        try:
            self.GetandReplaceButtons()
            global I_figure, I_ax, I_graph
            I_figure = plt.figure(figsize=(9,7), dpi=100)
            I_ax = I_figure.add_subplot(1, 1, 1)
            Graph = FigureCanvasTkAgg(I_figure, self.window)
            I_graph = Graph.get_tk_widget()
            I_graph.pack(side=RIGHT)
            self.current_graph = I_graph
            self.functions = self.newtext.split(',')
            line_colours = ['yellow', 'blue', 'red', 'green', 'cyan', 'magenta', 'white']
            loci = set()
            plt.axis([-20, 20, -20, 20])
            for i in range(len(self.functions)):
                Expression = Convert_Locus(self.functions[i])
                if Expression == False and 'arg(z' in self.functions[i]:
                    self.Centre_Graph_Axis()
                    Argument = Create_argument_equation(str(self.functions[i]))
                    equation = Argument[0]
                    point = Argument[-1]
                    x = np.linspace(-20, 20)
                    function = eval(equation)
                    plt.plot(x, function, color = line_colours[i], linestyle = 'dotted')
                    plt.axhline(y=point[-1], color = line_colours[i], label = str(self.functions[i]).replace('*j','i'))
                    plt.scatter(point[0], point[-1], color = line_colours[i])
                    I_ax.legend(loc='upper right')
                    
                elif Expression == False and isinstance(eval(self.functions[i]), complex) == True:
                    z = complex(eval(self.functions[i]))
                    self.Centre_Graph_Axis()
                    plt.scatter(z.real, z.imag, s=200, color=line_colours[i])
                    xy = (z.real, z.imag)
                    plt.annotate('z'+str(i+1)+': '+str(eval(self.functions[i])).replace('j','i'), xy)
                    
                else:
                    self.locus = Convert_Locus(self.functions[i])
                    if isinstance(self.locus[-1], int) == True or isinstance(self.locus[-1], float) == True :
                        Centre = self.locus[0]
                        radius = self.locus[-1]
                        self.Centre_Graph_Axis()
                        Locus = plt.Circle(Centre, radius, fill = False, edgecolor=line_colours[i])
                        plt.scatter(Centre[0], Centre[1], s=100, color = line_colours[i])
                        xy = Centre
                        plt.annotate(str(self.functions[i]).replace('*j','i'), xy)
                        I_ax.add_artist(Locus)
                        I_ax.add_patch(Locus)
                        
                    else:
                        self.Centre_Graph_Axis()
                        current_color = line_colours[i]
                        point1 = self.locus[0]
                        point2 = self.locus[-1]
                        Re = [point1[0], point2[0]]
                        Im = [point1[-1], point2[-1]]
                        plt.plot(Re, Im, color = current_color, marker = 'o')
                        x1 = point1[0]; x2 = point2[0]
                        y1 = point1[-1]; y2 = point2[-1]
                        #Midpoint = ((x1 + x2) / 2, (y1 + y2) / 2)
                        Mid_x = (x1 + x2) / 2; Mid_y = (y1 + y2) / 2
                        Mid_point = (Mid_x, Mid_y)
                        #Finding the equation of the line where the perpendicular gradient passes through the midpoint
                        #Perpendicular Gradient = -1 / ((y1 - y2) / (x1 - x2))
                        Perpendicular_gradient = -1 / ((y1 - y2) / (x1 - x2))
                        y_intercept = Mid_point[-1] - (Perpendicular_gradient * Mid_point[0])
                        #f(x) function to plot
                        x = np.linspace(-20, 20)
                        y = Perpendicular_gradient * x + y_intercept
                        plt.scatter(Mid_point[0], Mid_point[1], s=100, color=current_color)
                        plt.plot(x, y, color = current_color, linestyle='dotted', label = str(self.functions[i]).replace('*j','i'))
                        I_ax.legend(loc='upper right')
            I_ax.set_xlabel('Re(z)')
            I_ax.set_ylabel('Im(z)')
            plt.grid()
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.CF.delete(0, END)
            self.CF.insert(0, 'MATH - SYNTAX ERROR')

#SUBTASK 2. Create a 3D Graphics Feature
#- This feature should be able to plot 3D functions and data.
class Graphics3D(UserInterface):
    def __init__(self):
        self.window = window
        self.F = Entry(window, width=55, font=('Helvetica 20', 16), bg = 'gray8', fg = 'white')
        self.F.place(x=40, y=44)
        self.F.focus_set()
        self.Create_Graphics3D_Buttons()

    #Display an Empty 3D grid onto the right-hand side of the screen
    def Display_3D_Grid(self):
        plt.style.use('dark_background')
        global Grid_figure3D, Grid_ax3D, grid_3D
        Grid_figure3D = plt.figure(figsize=(8,7), dpi=100)
        Grid_ax3D = Grid_figure3D.add_subplot(1, 1, 1, projection='3d')
        Grid = FigureCanvasTkAgg(Grid_figure3D, self.window)
        grid_3D = Grid.get_tk_widget()
        grid_3D.pack(side=RIGHT)
        self.current_graph = grid_3D
        Grid_ax3D.set_xlabel('x')
        Grid_ax3D.set_ylabel('y')
        Grid_ax3D.set_zlabel('z')
        plt.grid()

    #Replace Buttons with their specified function
    def GetandReplaceButtons(self):
        try:
            Lower_Functions = ['asin(', 'acos(', 'atan(', 'sin(', 'cos(', 'tan(', 'cosec(', 'sec(' 'cot(']
            self.expression = self.F.get()
            self.newtext = self.expression.replace('×', '*')
            self.newtext = self.newtext.replace('%', '/100')
            self.newtext = self.newtext.replace('^','**')
            self.newtext = self.newtext.replace('³', '**3')
            self.newtext = self.newtext.replace('²','**2')
            self.newtext = self.newtext.replace('sqrt(','np.sqrt(')
            for lf in Lower_Functions:
                self.newtext = self.newtext.replace(lf, lf.capitalize())
            if self.newtext.find('z=') == 0:
                self.newtext = self.newtext.replace('z=', '')
            self.newtext = self.newtext.replace('=', '-1*')
            self.Convert_Functions()
            self.Convert_Algebraic_Letters()
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    def Create_Graphics3D_Buttons(self):
        #ROW1 BUTTONS
        #π, x, y, z, =, AC, DEL
        Button(self.window, text = 'π', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('π')).place(x=0,y=243)

        Button(self.window, text ='x', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('x')).place(x=55,y=243)

        Button(self.window, text ='y', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('y')).place(x=110,y=243)

        Button(self.window, text ='z', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('z')).place(x=165,y=243)
        
        Button(self.window, text ='=', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('=')).place(x=220,y=243)

        Button(self.window, text ='AC', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.clear()).place(x=275,y=243)

        Button(self.window, text ='DEL', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.DEL()).place(x=330,y=243)

        #ROW2 BUTTONS
        #Sin, Cos, Tan, Log, Ln, e, e^n
        Button(self.window, text = 'Sin', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Sin(')).place(x=0,y=286)

        Button(self.window, text ='Cos', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cos(')).place(x=55,y=286)

        Button(self.window, text ='Tan', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Tan(')).place(x=110,y=286)

        Button(self.window, text ='Log', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Log(')).place(x=165,y=286)
        
        Button(self.window, text ='Ln', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Ln(')).place(x=220,y=286)

        Button(self.window, text ='e', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('e')).place(x=275,y=286)

        Button(self.window, text ='eⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('e^')).place(x=330,y=286)

        #ROW3 BUTTONS
        #Asin, Acos, Atan, Sec, Cosec, Cot, ,
        Button(self.window, text = 'Asin', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('Asin(')).place(x=0,y=329)

        Button(self.window, text ='Acos', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Acos(')).place(x=55,y=329)

        Button(self.window, text ='Atan', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Atan(')).place(x=110,y=329)

        Button(self.window, text ='Sec', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Sec(')).place(x=165,y=329)
        
        Button(self.window, text ='Cosec', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cosec(')).place(x=220,y=329)

        Button(self.window, text ='Cot', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Cot(')).place(x=275,y=329)

        Button(self.window, text =',', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(',')).place(x=330,y=329)

        #ROW4 BUTTONS
        #9, 8, 7, (, ), x^3, x^2
        Button(self.window, text = '9', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('9')).place(x=0,y=372)

        Button(self.window, text ='8', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('8')).place(x=55,y=372)

        Button(self.window, text ='7', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('7')).place(x=110,y=372)

        Button(self.window, text ='(', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('(')).place(x=165,y=372)
        
        Button(self.window, text =')', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(')')).place(x=220,y=372)

        Button(self.window, text ='x³', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('³')).place(x=275,y=372)

        Button(self.window, text ='x²', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('²')).place(x=330,y=372)
        
        #ROW5 BUTTONS
        #6, 5, 4, +, ÷, ²√x, 1/x
        Button(self.window, text = '6', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('6')).place(x=0,y=415)

        Button(self.window, text ='5', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('5')).place(x=55,y=415)

        Button(self.window, text ='4', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('4')).place(x=110,y=415)

        Button(self.window, text ='+', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('+')).place(x=165,y=415)
        
        Button(self.window, text ='÷', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('/')).place(x=220,y=415)

        Button(self.window, text ='²√x', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('sqrt(')).place(x=275,y=415)

        Button(self.window, text ='1/x', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('1/')).place(x=330,y=415)

        #ROW6 BUTTONS
        #3, 2, 1, -, ×, |x|, x^n
        Button(self.window, text = '3', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('3')).place(x=0,y=458)

        Button(self.window, text ='2', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('2')).place(x=55,y=458)

        Button(self.window, text ='1', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('1')).place(x=110,y=458)

        Button(self.window, text ='-', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('-')).place(x=165,y=458)
        
        Button(self.window, text ='×', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('×')).place(x=220,y=458)

        Button(self.window, text ='|x|', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('abs(')).place(x=275,y=458)

        Button(self.window, text ='xⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('^')).place(x=330,y=458)

        #ROW7 BUTTONS
        #0, ., 10^n, %, Save, Exit, Exe
        Button(self.window, text = '0', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('0')).place(x=0,y=501)

        Button(self.window, text ='.', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('.')).place(x=55,y=501)

        Button(self.window, text ='10ⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('10^')).place(x=110,y=501)

        Button(self.window, text ='%', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('%')).place(x=165,y=501)
        
        Button(self.window, text ='Save', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.Save_Graph()).place(x=220,y=501)

        Button(self.window, text ='Exit', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.remove_plot(self.current_graph)).place(x=275,y=501)

        Button(self.window, text ='Exe', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.execute()).place(x=330,y=501)

        self.window.bind('<Return>',lambda event: self.execute())

    #Add functionality to buttons
    def action(self, argi):
        self.F.insert(END,argi)

    def clear(self):
        self.F.delete(0,END)
 
    def DEL(self):
        self.expression = self.F.get()
        self.expression = self.expression[0:-1]
        self.F.delete(0,END)
        self.F.insert(END,self.expression)

    #Replaces Trigonometric and Logarithmic functions with the necessary operators
    def Convert_Functions(self):
        Functions = ['Sin(', 'Cos(', 'Tan(', 'Sec(', 'Cosec(', 'Cot(', 'Log(', 'Ln(', 'Asin (', 'Acos(', 'Atan(']
        Symbols = ['x', 'y', 'z', 'π', 'e']
        try:
            self.newtext = self.newtext.replace('ASin(', 'Asin(')
            self.newtext = self.newtext.replace('ACos(', 'Acos(')
            self.newtext = self.newtext.replace('ATan(', 'Atan(')
            for i in range(0, 10):
                for j in Functions:
                    self.newtext = self.newtext.replace(str(i)+j, str(i)+'*'+j)
            for i in Symbols:
                for j in Functions:
                    self.newtext = self.newtext.replace(i+j, i+'*'+j)
            self.newtext = self.newtext.replace('Sin(','np.sin(')
            self.newtext = self.newtext.replace('Cos(','np.cos(')
            self.newtext = self.newtext.replace('Tan(','np.tan(')
            self.newtext = self.newtext.replace('Sec(','1/np.cos(')
            self.newtext = self.newtext.replace('Cosec(','1/np.sin(')
            self.newtext = self.newtext.replace('Cot(','1/np.tan(')
            self.newtext = self.newtext.replace('Log(','np.log(')
            self.newtext = self.newtext.replace('Ln(','np.log10(')
            self.newtext = self.newtext.replace('Asin(','np.arcsin(')
            self.newtext = self.newtext.replace('Acos(','np.arccos(')
            self.newtext = self.newtext.replace('Atan(','np.arctan(')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    #Converts Algebraic letters so that they can be evaluated and outputted in a graph
    def Convert_Algebraic_Letters(self):
        Symbols = ['x', 'y', 'z', 'π', 'e']
        try:
            self.newtext = self.newtext.replace('ππ', 'π**2')
            self.newtext = self.newtext.replace('yy', 'y**2')
            self.newtext = self.newtext.replace('xx', 'x**2')
            self.newtext = self.newtext.replace('zz', 'z**2')
            self.newtext = self.newtext.replace('ee', 'e**2')
            for i in range(0, 10):
                for j in Symbols:
                    self.newtext = self.newtext.replace(str(i)+j, str(i)+'*'+j)
            for i in Symbols:
                for j in Symbols:
                    self.newtext = self.newtext.replace(i+j, i+'*'+j)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')

    #Removes Plot on the screen and allows the user to plot another graph
    def remove_plot(self, graph):
        graph.pack_forget()

    #Allows the user to save their Graph as a png file
    def Save_Graph(self):
        plt.savefig(str(self.expression)+'.png')

    #Replaces Curves with necessary operators so users can understand what the plot is
    def Replace_Labels(self):
        self.expression = self.expression.replace('asin', 'arcsin(')
        self.expression = self.expression.replace('Asin(', 'arcsin(')
        self.expression = self.expression.replace('acos', 'arccos(')
        self.expression = self.expression.replace('Acos(', 'arccos(')
        self.expression = self.expression.replace('atan', 'arctan(')
        self.expression = self.expression.replace('Atan(', 'arctan(')
        self.expression = self.expression.replace('x^2', 'x²')
        self.expression = self.expression.replace('x^3', 'x³')
        
    #Plots a graph based on the data entered into the F entry box
    def execute(self):
        plt.style.use('dark_background')
        try:
            self.GetandReplaceButtons()
            global figure_3D, ax_3D, graph_3D
            self.remove_plot(self.current_graph)
            self.functions = self.newtext.split(',')
            line_colours = ['yellow', 'blue', 'red', 'green', 'cyan', 'magenta', 'white']
            figure_3D = plt.figure(figsize=(8,7), dpi=100)
            ax_3D = figure_3D.add_subplot(1, 1, 1, projection='3d')
            Graph_3D = FigureCanvasTkAgg(figure_3D, self.window)
            graph_3D = Graph_3D.get_tk_widget()
            graph_3D.pack(side=RIGHT)
            self.current_graph = graph_3D
            self.functions = self.newtext.split(',')
            for i in range(len(self.functions)):
                self.Replace_Labels()
                Label = str(self.expression.split(',')[i])
                if 'z' not in Label and '=' not in Label:
                    Label = 'z = '+str(Label)
                else:
                    Label = str(Label)
                if make_z_subject(self.functions[i]) == False:
                    x = np.linspace(-20, 20, 100)
                    y = np.linspace(-20, 20, 100)
                    z = np.linspace(-20, 20, 100)
                    x, y = np.meshgrid(x, y)
                    self.function = eval(self.functions[i])
                    plane = ax_3D.plot_surface(x, y, self.function, color = line_colours[i], label = 'Π'+str(i+1)+': '+Label)
                elif make_z_subject(self.functions[i]) != False:
                    x = np.linspace(-20, 20, 100)
                    y = np.linspace(-20, 20, 100)
                    z = np.linspace(-20, 20, 100)
                    x, y = np.meshgrid(x, y)
                    self.function = make_z_subject(self.function[i])
                    plane = ax_3D.plot_surface(x, y, self.function, color = line_colours[i], label = 'Π'+str(i+1)+': '+Label)
                plane._facecolors2d=plane._facecolor3d
                plane_edgecolors2d=plane._edgecolor3d
            ax_3D.legend()
            ax_3D.set_xlabel('x')
            ax_3D.set_ylabel('y')
            ax_3D.set_zlabel('z')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError, ValueError):
            self.F.delete(0, END)
            self.F.insert(0, 'MATH - SYNTAX ERROR')
            
#6. Create a Computational Calculator feature:
# - It should be able to handle number bases and Boolean algebra.
# - In addition, it should be able to plot graphs & trees and perform algorithms on a set of data.
class Computational_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.Isupper = True
        self.equation = Entry(window, width = 25, font=('Helvetica 20',16), bd=30, bg = 'gray8', fg = 'white')
        self.equation. place(x=0, y=0)
        self.equation.focus_set()
        self.Create_Computational_Buttons()

    #Replace symbols with the necessarry operator 
    def GetandReplaceButtons(self):
        try:
            self.expression = self.equation.get()
            self.newtext = self.expression.replace('^', '**')
            self.newtext = self.newtext.replace('³', '**3')
            self.newtext = self.newtext.replace('²','**2')
            self.newtext = self.newtext.replace('XOR', '^')
            self.newtext = self.newtext.replace('AND', ' and ')
            self.newtext = self.newtext.replace('OR', ' or ')
            self.newtext = self.newtext.replace('NOT', ' not ')
            self.newtext = self.newtext.replace('=', '==')
            self.newtext = self.newtext.replace('<==', '<=')
            self.newtext = self.newtext.replace('>==', '>=')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.expression.delete(0,END)
            self.expression.insert(0,'MATH - SYNTAX ERROR')
        

    def Create_Computational_Buttons(self):
        #Create ROW 1 Butons
        #A, B, C, D, E, F, G, H,
        Button(self.window, text='A', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('A')).place(x=0, y=85)

        Button(self.window, text='B', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('B')).place(x=45, y=85)

        Button(self.window, text='C', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('C')).place(x=90, y=85)

        Button(self.window, text='D', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('D')).place(x=135, y=85)

        Button(self.window, text='E', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('E')).place(x=180, y=85)

        Button(self.window, text='F', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('F')).place(x=225, y=85)

        Button(self.window, text='G', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('G')).place(x=270, y=85)

        Button(self.window, text='H', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('H')).place(x=315, y=85)

        #Create ROW 2 Buttons
        #I, J, K, L, M, N, O, P
        Button(self.window, text='I', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('I')).place(x=0, y=125)

        Button(self.window, text='J', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('J')).place(x=45, y=125)

        Button(self.window, text='K', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('K')).place(x=90, y=125)

        Button(self.window, text='L', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('L')).place(x=135, y=125)

        Button(self.window, text='M', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('M')).place(x=180, y=125)

        Button(self.window, text='N', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('N')).place(x=225, y=125)

        Button(self.window, text='O', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('O')).place(x=270, y=125)

        Button(self.window, text='P', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('P')).place(x=315, y=125)


        #Create ROW 3 Buttons
        #Q, R, S, T, U, V, W, X
        Button(self.window, text='Q', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('Q')).place(x=0, y=165)

        Button(self.window, text='R', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('R')).place(x=45, y=165)

        Button(self.window, text='S', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('S')).place(x=90, y=165)

        Button(self.window, text='T', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('T')).place(x=135, y=165)

        Button(self.window, text='U', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('U')).place(x=180, y=165)

        Button(self.window, text='V', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('V')).place(x=225, y=165)

        Button(self.window, text='W', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('W')).place(x=270, y=165)

        Button(self.window, text='X', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('X')).place(x=315, y=165)

        #Create ROW 4 Buttons
        #Y,Z, LOWER, AND, OR, NOT, XOR
        Button(self.window, text='Y', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('Y')).place(x=0, y=205)

        Button(self.window, text='Z', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('Z')).place(x=45, y=205)

        Button(self.window, text='LOWER', font=('Helvetica 20',16), width=7, height=1,
               fg ='white', bg='black', command = lambda: self.Swap_Case()).place(x=90, y=205)

        Button(self.window, text='AND', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action(' AND ')).place(x=180, y=205)
        
        Button(self.window, text='NOT', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action(' NOT ')).place(x=225, y=205)

        Button(self.window, text='OR', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action(' OR ')).place(x=270, y=205)

        Button(self.window, text='XOR', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action(' XOR ')).place(x=315, y=205)

        #Create ROW 5 Buttons
        #7, 8, 9, <, >, =, /, sqrt
        Button(self.window, text='7', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('7')).place(x=0, y=245)

        Button(self.window, text='8', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('8')).place(x=45, y=245)

        Button(self.window, text='9', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('9')).place(x=90, y=245)

        Button(self.window, text='<', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('<')).place(x=135, y=245)

        Button(self.window, text='>', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('>')).place(x=180, y=245)

        Button(self.window, text='=', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('=')).place(x=225, y=245)

        Button(self.window, text='/', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('/')).place(x=270, y=245)

        Button(self.window, text='²√x', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.sqrt()).place(x=315, y=245)

        #Create ROW 6 Buttons
        #6, 5, 4, *, x^2, x^3, BIN, OCT
        Button(self.window, text='6', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('6')).place(x=0, y=285)

        Button(self.window, text='5', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('5')).place(x=45, y=285)

        Button(self.window, text='4', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('4')).place(x=90, y=285)

        Button(self.window, text='*', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('*')).place(x=135, y=285)

        Button(self.window, text='x²', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('²')).place(x=180, y=285)

        Button(self.window, text='xⁿ', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('^')).place(x=225, y=285)

        Button(self.window, text='Bin', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.Convert_to_binary()).place(x=270, y=285)

        Button(self.window, text='Oct', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.Convert_to_oct()).place(x=315, y=285)
        
        #Create ROW 7 Buttoms
        #3, 2, 1, -,  (, ), HEX, DEC
        Button(self.window, text='3', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('3')).place(x=0, y=325)

        Button(self.window, text='2', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('2')).place(x=45, y=325)

        Button(self.window, text='1', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('1')).place(x=90, y=325)

        Button(self.window, text='-', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('-')).place(x=135, y=325)

        Button(self.window, text='(', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('(')).place(x=180, y=325)

        Button(self.window, text=')', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action(')')).place(x=225, y=325)

        Button(self.window, text='Hex', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.Convert_to_hex()).place(x=270, y=325)

        Button(self.window, text='Dec', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.Convert_to_denary()).place(x=315, y=325)
        

        #Create ROW 8 Buttons
        #0, ., %, +, RND, AC, DEL, =
        Button(self.window, text='0', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('0')).place(x=0, y=365)

        Button(self.window, text='.', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('.')).place(x=45, y=365)

        Button(self.window, text='%', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('%')).place(x=90, y=365)

        Button(self.window, text='+', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.action('+')).place(x=135, y=365)

        Button(self.window, text='Rnd', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.round()).place(x=180, y=365)

        Button(self.window, text='AC', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.clear()).place(x=225, y=365)

        Button(self.window, text='DEL', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.DEL()).place(x=270, y=365)

        Button(self.window, text='EXE', font=('Helvetica 20',16), width=3, height=1,
               fg ='white', bg='black', command = lambda: self.execute()).place(x=315, y=365)

        self.window.bind('<Return>',lambda event: self.execute())

    #Add functionality to the buttons
    def action(self, argi):
        if self.Isupper == True:
            self.equation.insert(END, argi)
        elif self.Isupper != True and len(argi) == 1:
            self.equation.insert(END, argi.lower())
        elif len(argi) > 4:
            self.equation.insert(END, argi)
        
    def clear(self):
        self.equation.delete(0,END)
     
    def DEL(self):
        self.expression = self.equation.get()
        self.expression = self.expression[0:-1]
        self.equation.delete(0,END)
        self.equation.insert(END,self.expression)

    #Returns a value when the equals button is clicked
    def execute(self):
        try:
            self.expression = self.equation.get()
            if self.expression.isalpha() == True:
                self.get_unicode_value()
                self.value = self.unicode_value
            else:
                self.GetandReplaceButtons()
                self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.equation.delete(0,END)
            self.equation.insert(0, self.value)

    #Rounds up numbers to 3 significant figures
    def round(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.equation.delete(0,END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.rounded = round(self.value, 2)
            self.equation.delete(0, END)
            self.equation.insert(0, self.rounded)

    #Performs the square root operator on numbers
    def sqrt(self):
        try:
            self.GetandReplaceButtons()
            self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.equation.delete(0, END)
            self.equation.insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.sqrtval = self.value ** 0.5
            self.equation.delete(0, END)
            self.equation.insert(0, self.sqrtval)


    #This function will return the unicode value of string based on its numerical position in the table
    def get_unicode_value(self):
        self.unicode_value = 0
        for char in self.expression:
            self.unicode_value += ord(char)
        
    def Swap_Case(self):
        if self.Isupper == True:
            self.Isupper = False
        elif self.Isupper == False:
            self.Isupper = True

    #This function will convert and expression entered into binary representation
    def Convert_to_binary(self):
        try:
            self.expression = self.equation.get()
            if self.expression.isalpha() == True:
                self.get_unicode_value()
                self.value = self.unicode_value
            else:
                self.GetandReplaceButtons()
                self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.equation.delete(0, END)
            self.equation .insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.value = bin(self.value).replace('0b','')
            self.equation.delete(0, END)
            self.equation.insert(0, str(self.value))

    #Converts an expression into a hexadecimal representation
    def Convert_to_hex(self):
        try:
            self.expression = self.equation.get()
            if self.expression.isalpha() == True:
                self.get_unicode_value()
                self.value = self.unicode_value
            else:
                self.GetandReplaceButtons()
                self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.equation.delete(0, END)
            self.equation .insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.value = hex(self.value).replace('0x','').capitalize()
            self.equation.delete(0, END)
            self.equation.insert(0, str(self.value))

    #Converts an expression into a octal representation
    def Convert_to_oct(self):
        try:
            self.expression = self.equation.get()
            if self.expression.isalpha() == True:
                self.get_unicode_value()
                self.value = self.unicode_value
            else:
                self.GetandReplaceButtons()
                self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.equation.delete(0, END)
            self.equation .insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.value = oct(self.value).replace('0o','')
            self.equation.delete(0, END)
            self.equation.insert(0, str(self.value))


    #Converts an expression into a decimal representation
    def Convert_to_denary(self):
        try:
            self.expression = self.equation.get()
            if self.expression.isalpha() == True:
                self.get_unicode_value()
                self.value = self.unicode_value
            else:
                self.GetandReplaceButtons()
                self.value = eval(self.newtext)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.equation.delete(0, END)
            self.equation .insert(0, 'MATH - SYNTAX ERROR')
        else:
            self.value = int(self.value)
            self.equation.delete(0, END)
            self.equation.insert(0, str(self.value))
                
        

#SUBTASK 1. Create a Graph theory feature
#- This feature should be able to plot Graph data structrues
#- It should also be able to represent them in Adjacency lists and Matices
#- In addition, it should be able to perform traversal and optimisation algorithms
class Graph_Theory_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.Vertices = Entry(window, width = 50, font=('Helvetica 20',18), bg = 'gray8', fg = 'white')
        self.Vertices.place(x=30, y=40)
        self.Vertices.focus_set()#Sets focus on the input text area
        self.Edges = Entry(self.window, width = 50, font = ('Helvetica 20',18), bg = 'gray8', fg='white')
        self.Edges.place(x=30, y=77)
        self.Output = scrolledtext.ScrolledText(self.window, wrap = WORD, width=30, height=10,
                                                font = ('Helvetica 20',18), bg ='gray8', fg='white')
        self.Output.place(x=0, y=595)
        self.Create_Graph_Buttons()

    #Replaces strings with their necessary operators
    def GetandReplaceButtons(self):
        try:
            global V, E
            V = self.Vertices.get()
            E = self.Edges.get()
            if ',' in V:
                V = V.split(',')
            self.newtext = E.replace('^','**')
            self.newtext = self.newtext.replace('³', '**3')
            self.newtext = self.newtext.replace('²','**2')
            self.newtext = self.newtext.replace(' ', '')
            self.newtext = self.newtext.replace('ππ', 'π**2')
            for i in range(10):
                self.newtext = self.newtext.replace(str(i)+'π', str(i)+'*π')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Edges.delete(0,END)
            self.Edges.insert(0, 'MATH - SYNTAX ERROR')
        

    def Create_Graph_Buttons(self):
        #ROW1 BUTTONS
        #A,B,C,D,E,F,G
        Button(self.window, text ='A', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('A')).place(x=0,y=157)

        Button(self.window, text ='B', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('B')).place(x=55,y=157)

        Button(self.window, text ='C', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('C')).place(x=110,y=157)

        Button(self.window, text ='D', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('D')).place(x=165,y=157)
        
        Button(self.window, text ='E', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('E')).place(x=220,y=157)

        Button(self.window, text ='F', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('F')).place(x=275,y=157)

        Button(self.window, text ='G', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('G')).place(x=330,y=157)

        #ROW2 BUTTONS
        #H,I,J,K,L,M,N
        Button(self.window, text ='H', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('H')).place(x=0,y=200)

        Button(self.window, text ='I', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('I')).place(x=55,y=200)

        Button(self.window, text ='J', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('J')).place(x=110,y=200)

        Button(self.window, text ='K', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('K')).place(x=165,y=200)
        
        Button(self.window, text ='L', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('L')).place(x=220,y=200)

        Button(self.window, text ='M', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('M')).place(x=275,y=200)

        Button(self.window, text ='N', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('N')).place(x=330,y=200)

        #ROW3 BUTTONS
        #O,P,Q,R,S,T,U
        Button(self.window, text ='O', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('O')).place(x=0,y=243)

        Button(self.window, text ='P', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('P')).place(x=55,y=243)

        Button(self.window, text ='Q', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Q')).place(x=110,y=243)

        Button(self.window, text ='R', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('R')).place(x=165,y=243)
        
        Button(self.window, text ='S', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('S')).place(x=220,y=243)

        Button(self.window, text ='T', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('T')).place(x=275,y=243)

        Button(self.window, text ='U', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('U')).place(x=330,y=243)
        

        #ROW4 BUTTONS
        #V,W,X,Y,Z,pi,e
        Button(self.window, text ='V', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('V')).place(x=0,y=286)

        Button(self.window, text ='W', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('W')).place(x=55,y=286)

        Button(self.window, text ='X', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('X')).place(x=110,y=286)

        Button(self.window, text ='Y', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Y')).place(x=165,y=286)
        
        Button(self.window, text ='Z', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Z')).place(x=220,y=286)

        Button(self.window, text ='π', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('π')).place(x=275,y=286)

        Button(self.window, text ='e', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('2.718281828459045')).place(x=330,y=286)

        #ROW5 BUTTONS
        #x^3,x^2,x^n,e^n,(,),,
        Button(self.window, text ='x³', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('³')).place(x=0,y=329)

        Button(self.window, text ='x²', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('²')).place(x=55,y=329)

        Button(self.window, text ='xⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('^')).place(x=110,y=329)

        Button(self.window, text ='eⁿ', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('2.718281828459045^')).place(x=165,y=329)
        
        Button(self.window, text ='(', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('(')).place(x=220,y=329)

        Button(self.window, text =')', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(')')).place(x=275,y=329)

        Button(self.window, text =',', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action(',')).place(x=330,y=329)
        
        #ROW6 BUTTONS
        #9,8,7,+,*,DFS,AList
        Button(self.window, text ='9', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('9')).place(x=0,y=372)

        Button(self.window, text ='8', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('8')).place(x=55,y=372)

        Button(self.window, text ='7', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('7')).place(x=110,y=372)

        Button(self.window, text ='+', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('+')).place(x=165,y=372)
        
        Button(self.window, text ='*', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('*')).place(x=220,y=372)

        Button(self.window, text ='DFS', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.Depth_First_Search()).place(x=275,y=372)

        Button(self.window, text ='AdjList', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.AdjList()).place(x=330,y=372)

        #ROW7 BUTTONS
        #6,5,4,-,% BFS,AMatrix
        Button(self.window, text ='6', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('6')).place(x=0,y=415)

        Button(self.window, text ='5', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('5')).place(x=55,y=415)

        Button(self.window, text ='4', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('4')).place(x=110,y=415)

        Button(self.window, text ='-', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('-')).place(x=165,y=415)
        
        Button(self.window, text ='%', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('%')).place(x=220,y=415)

        Button(self.window, text ='BFS', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.Breadth_First_Search()).place(x=275,y=415)

        Button(self.window, text ='AdjMatrix', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.AdjMat()).place(x=330,y=415)

        #ROW8 BUTTONS
        #3,2,1,/,Djikstra
        Button(self.window, text ='3', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('3')).place(x=0,y=458)

        Button(self.window, text ='2', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('2')).place(x=55,y=458)

        Button(self.window, text ='1', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('1')).place(x=110,y=458)

        Button(self.window, text ='/', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('/')).place(x=165,y=458)
        
        Button(self.window, text ='Djikstra', font=('Helvetica 20',10), width = 20, height=2, fg ='white',
               bg = 'black', command = lambda: self.Djikstra_Algorithm()).place(x=220,y=458)

        #ROW9 BUTTONS
        #0,.,10^n,Save,draw,Exit,Exe
        Button(self.window, text ='0', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('0')).place(x=0,y=501)

        Button(self.window, text ='.', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('.')).place(x=55,y=501)

        Button(self.window, text ='Save', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.Save_Graph()).place(x=110,y=501)

        Button(self.window, text ='Exit', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.remove_plot()).place(x=165,y=501)
        
        Button(self.window, text ='AC', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command =lambda: self.clear()).place(x=220,y=501)

        Button(self.window, text ='DEL', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.DEL()).place(x=275,y=501)

        Button(self.window, text ='Draw', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.Draw()).place(x=330,y=501)

        self.window.bind('<Return>',lambda event: self.Draw())
        
    #Add functionality to buttons
    def action(self, argi):
        self.Edges.insert(END, argi)

    def clear(self):
        self.Vertices.delete(0,END)
        self.Edges.delete(0,END)
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
 
    def DEL(self):
        self.expression = self.Edges.get()
        self.expression = self.expression[0:-1]
        self.Edges.delete(0,END)
        self.Edges.insert(END,self.expression)

    #This Function displays an Adjacency List in the Output box on the UI 
    def AdjList(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            G = Graph(V, self.newtext)
            G.AdjacencyList()
            self.Output.insert(INSERT, 'G | ADJACENCY LIST')
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '==================')
            self.Output.insert(INSERT, '\n')
            for List in G.gdict:
                self.Output.insert(INSERT, str(List)+'-->'+str(G.gdict.get(List)))
                self.Output.insert(INSERT, '\n')
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Edges.delete(0,END)
            self.Edges.insert(0,'MATH - SYNTAX ERROR')

    #This Function displays an Adjacency Matrix in the Output box on the UI 
    def AdjMat(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            G = Graph(V, self.newtext)
            Vx = list(sorted(G.vertices))
            G.AdjacencyMatrix()
            self.Output.insert(INSERT, 'G | ADJACENCY MATRIX')
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '====================')
            self.Output.insert(INSERT, '\n')
            for i, matrix in enumerate(G.gmatrix):
                self.Output.insert(INSERT, ((str(Vx[i])+' '+str(matrix)).replace('. ',',')).replace(',   ]',']'))
                self.Output.insert(INSERT, '\n')
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Edges.delete(0,END)
            self.Edges.insert(0,'MATH - SYNTAX ERROR')

    #Performs the Depth first search algorithm based on the graph edges:
    def Depth_First_Search(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            G = Graph(V, self.newtext)
            Vx = list(sorted(G.vertices))
            self.Output.insert(INSERT, 'Depth-First-Search Traversal')
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '======================')
            self.Output.insert(INSERT, '\n')
            Solutions = list(G.DFS())
            for pos, node in enumerate(Vx):
                self.Output.insert(INSERT, 'Start node '+str(node)+': '+str(Solutions[pos]))
                self.Output.insert(INSERT, '\n')
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Edges.delete(0,END)
            self.Edges.insert(0,'MATH - SYNTAX ERROR')


    #Performs the Breadth first search algorithm based on the graph edges
    def Breadth_First_Search(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            G = Graph(V, self.newtext)
            Vx = list(sorted(G.vertices))
            self.Output.insert(INSERT, 'Breadth-First-Search Traversal')
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '========================')
            self.Output.insert(INSERT, '\n')
            Solutions = list(G.BFS())
            for pos, node in enumerate(Vx):
                self.Output.insert(INSERT, 'Start node '+str(node)+': '+str(Solutions[pos]))
                self.Output.insert(INSERT, '\n')
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Edges.delete(0,END)
            self.Edges.insert(0,'MATH - SYNTAX ERROR')

    #Performs djikstra's algorithm based on the graph edges
    def Djikstra_Algorithm(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            G = Graph(V, self.newtext)
            Vx = list(sorted(G.vertices))
            self.Output.insert(INSERT, "Djikstra's Algorithm")
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '==============')
            self.Output.insert(INSERT, '\n')
            random_vertex = random.choice(Vx)
            self.Output .insert(INSERT, 'Source Node: '+str(random_vertex))
            self.Output.insert(INSERT, '\n')
            Solutions = list(G.Djikstra(Vx.index(random_vertex)))
            self.Output.insert(INSERT, "Vertex \t Shortest Distance")
            self.Output.insert(INSERT, '\n')
            for i, distance in enumerate(Solutions):
                self.Output.insert(INSERT, str(Vx[i])+"\t\t"+str(round(distance, 4)))
                self.Output.insert(INSERT, '\n')
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Edges.delete(0,END)
            self.Edges.insert(0,'MATH - SYNTAX ERROR')
        
                
    #This Function removes the graph displayed onto the screen
    def remove_plot(self):
        try:
            self.current_graph.pack_forget()
        except AttributeError:
            pass

    #Allows the user to save their Graph as a png file
    def Save_Graph(self):
        plt.savefig('Graph.png')
                
    #output the Graph onto the grid based on the node and edge connections
    def Draw(self):
        try:
            self.GetandReplaceButtons()
            self.remove_plot()
            G = Graph(V, self.newtext)
            global graph_ds
            figure = plt.figure(figsize=(8,6), dpi=100)
            Ds = FigureCanvasTkAgg(figure, self.window)
            graph_ds = Ds.get_tk_widget()
            graph_ds.pack(side=RIGHT)
            self.current_graph = graph_ds
            G.DrawGraph()
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.remove_plot()
            self.Edges.delete(0,END)
            self.Edges.insert(0,'MATH - SYNTAX ERROR')


#SUBTASK 2. Create a Binary Tree calculator:
#-It should be able to draw Binary Trees
#-It should also be able to perform traversal algorithms like In-order, pre-order and post-order traversal.
#Binary Tree Calculator class
class Binary_Tree_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.nodes = Entry(window, width = 50, font=('Helvetica 20',18), bg = 'gray8', fg = 'white')
        self.nodes.place(x=30, y=40)
        self.nodes.focus_set()#Sets focus on the input text area
        self.Output = scrolledtext.ScrolledText(self.window, wrap = WORD, width=35, height=10,
                                                font = ('Helvetica 20',18), bg ='gray8', fg='white')
        self.Output.place(x=0, y=559)
        self.Tree = scrolledtext.ScrolledText(self.window, wrap = WORD, width=50, height=25,
                                              font = ('Helvetica 20',30), bg ='gray8', fg='white')
        self.Tree.place(x=500, y=150)
        self.Create_Binary_Tree_Buttons()

    #Replaces strings with their necessary operators
    def GetandReplaceButtons(self):
        try:
            global Vt
            Vt = self.nodes.get()
            self.newtext = Vt.replace('(','')
            self.newtext = self.newtext.replace(')', '')
            if ',' in self.newtext:
                self.newtext = self.newtext.split(',')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.nodes.delete(0,END)
            self.nodes.insert(0,'MATH - SYNTAX ERROR')
        
    def Create_Binary_Tree_Buttons(self):
        #ROW1 BUTTONS
        #A,B,C,D,E,F,G
        Button(self.window, text ='A', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('A')).place(x=0,y=157)

        Button(self.window, text ='B', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('B')).place(x=55,y=157)

        Button(self.window, text ='C', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('C')).place(x=110,y=157)

        Button(self.window, text ='D', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('D')).place(x=165,y=157)
        
        Button(self.window, text ='E', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('E')).place(x=220,y=157)

        Button(self.window, text ='F', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('F')).place(x=275,y=157)

        Button(self.window, text ='G', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('G')).place(x=330,y=157)

        #ROW2 BUTTONS
        #H,I,J,K,L,M,N
        Button(self.window, text ='H', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('H')).place(x=0,y=200)

        Button(self.window, text ='I', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('I')).place(x=55,y=200)

        Button(self.window, text ='J', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('J')).place(x=110,y=200)

        Button(self.window, text ='K', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('K')).place(x=165,y=200)
        
        Button(self.window, text ='L', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('L')).place(x=220,y=200)

        Button(self.window, text ='M', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('M')).place(x=275,y=200)

        Button(self.window, text ='N', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('N')).place(x=330,y=200)

        #ROW3 BUTTONS
        #O,P,Q,R,S,T,U
        Button(self.window, text ='O', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('O')).place(x=0,y=243)

        Button(self.window, text ='P', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('P')).place(x=55,y=243)

        Button(self.window, text ='Q', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Q')).place(x=110,y=243)

        Button(self.window, text ='R', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('R')).place(x=165,y=243)
        
        Button(self.window, text ='S', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('S')).place(x=220,y=243)

        Button(self.window, text ='T', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('T')).place(x=275,y=243)

        Button(self.window, text ='U', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('U')).place(x=330,y=243)

        #ROW4 BUTTONS
        #V,W,X,Y,Z,AC,DEL
        Button(self.window, text ='V', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('V')).place(x=0,y=286)

        Button(self.window, text ='W', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('W')).place(x=55,y=286)

        Button(self.window, text ='X', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('X')).place(x=110,y=286)

        Button(self.window, text ='Y', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Y')).place(x=165,y=286)
        
        Button(self.window, text ='Z', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('Z')).place(x=220,y=286)

        Button(self.window, text ='AC', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.clear()).place(x=275,y=286)

        Button(self.window, text ='DEL', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.DEL()).place(x=330,y=286)

        #ROW5 BUTTONS
        #IN-ORDER, PRE-ORDER, POST-ORDER, ,
        Button(self.window, text ='IN-ORDER', font=('Helvetica 20',10), width=13, height=2, fg='white',
               bg = 'black', command = lambda: self.Inorder_Traversal()).place(x=0,y=329)

        Button(self.window, text ='PRE-ORDER', font=('Helvetica 20',10), width = 13, height=2, fg ='white',
               bg = 'black', command = lambda: self.Preorder_Traversal()).place(x=109,y=329)

        Button(self.window, text ='POST-ORDER', font=('Helvetica 20',10), width = 13, height=2, fg ='white',
               bg = 'black', command = lambda: self.Postorder_Traversal()).place(x=218,y=329)

        Button(self.window, text =',', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action(',')).place(x=330,y=329)

        #ROW6 BUTTONS
        #9,8,7,6,5,4,3
        Button(self.window, text ='9', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('9')).place(x=0,y=372)

        Button(self.window, text ='8', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('8')).place(x=55,y=372)

        Button(self.window, text ='7', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('7')).place(x=110,y=372)

        Button(self.window, text ='6', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('6')).place(x=165,y=372)
        
        Button(self.window, text ='5', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('5')).place(x=220,y=372)

        Button(self.window, text ='4', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('4')).place(x=275,y=372)

        Button(self.window, text ='3', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('3')).place(x=330,y=372)
        
        #ROW7 BUTTONS
        #2,1,0,(,),SAVE DRAW
        Button(self.window, text ='2', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.action('2')).place(x=0,y=415)

        Button(self.window, text ='1', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('1')).place(x=55,y=415)

        Button(self.window, text ='0', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('0')).place(x=110,y=415)

        Button(self.window, text ='(', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action('(')).place(x=165,y=415)
        
        Button(self.window, text =')', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black', command = lambda: self.action(')')).place(x=220,y=415)

        Button(self.window, text ='Save', font=('Helvetica 20',10), width = 6, height=2, fg ='white',
               bg = 'black').place(x=275,y=415)

        Button(self.window, text ='Draw', font=('Helvetica 20',10), width=6, height=2, fg='white',
               bg = 'black', command = lambda: self.Draw_Binary_Tree()).place(x=330,y=415)

        self.window.bind('<Return>',lambda event: self.Draw_Binary_Tree())

    #Add functionality to buttons
    def action(self, argi):
        self.nodes.insert(END, argi)

    def clear(self):
        self.nodes.delete(0,END)
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
 
    def DEL(self):
        self.expression = self.nodes.get()
        self.expression = self.expression[0:-1]
        self.nodes.delete(0,END)
        self.nodes.insert(END,self.expression)

    #Performs the inorder traversal algorithm on a set of vertices and outputs it into the output box  
    def Inorder_Traversal(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            self.Output.insert(INSERT, 'In-order Traversal')
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '==================')
            self.Output.insert(INSERT, '\n')
            root = Binary_Tree(self.newtext[0])
            for pos, node in enumerate(self.newtext):
                if pos != 0:
                    root.insert_node(node)
            self.Output.insert(INSERT, str(root.inorder(root)))
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Output.delete(0,END)
            self.Output.insert(0,'MATH - SYNTAX ERROR')

    #Performs the Preorder traversal algorithm on a set of vertices and outputs it into the output box 
    def Preorder_Traversal(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            self.Output.insert(INSERT, 'Pre-order Traversal')
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '===================')
            self.Output.insert(INSERT, '\n')
            root = Binary_Tree(self.newtext[0])
            for pos, node in enumerate(self.newtext):
                if pos != 0:
                    root.insert_node(node)
            self.Output.insert(INSERT, str(root.preorder(root)))
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Output.delete(0,END)
            self.Output.insert(0,'MATH - SYNTAX ERROR')

    #Performs the Postorder traversal algorithm on a set of vertices and outputs it into the output box 
    def Postorder_Traversal(self):
        self.Output.configure(state='normal')
        self.Output.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            self.Output.insert(INSERT, 'Post-order Traversal')
            self.Output.insert(INSERT, '\n')
            self.Output.insert(INSERT, '====================')
            self.Output.insert(INSERT, '\n')
            BST = build(self.newtext)
            self.Output.insert(INSERT, (str(BST.postorder).replace('Node(','')).replace(')',''))
            self.Output.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Output.delete(0,END)
            self.Output.insert(0,'MATH - SYNTAX ERROR')

    #Draws the possible look of the Binary tree and outputs it onto the right hand side
    def Draw_Binary_Tree(self):
        self.Tree.configure(state='normal')
        self.Tree.delete('1.0',END)
        try:
            self.GetandReplaceButtons()
            self.Tree.insert(INSERT, 'Binary Tree Implementation')
            self.Tree.insert(INSERT, '\n')
            self.Tree.insert(INSERT, '=====================')
            self.Tree.insert(INSERT, '\n')
            BST = build(self.newtext)
            self.Tree.insert(INSERT, BST)
            self.Tree.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.Tree.delete(0,END)
            self.Tree.insert(0,'MATH - SYNTAX ERROR')


#SUBTASK 3 - Create an Infix convertor
#- It should be able to convert infix notation into postfix notation
#- Then output the solution below
class RPN_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.infix = Entry(window, width = 50, font=('Helvetica 20',18),
                           bd=30, bg = 'gray8', fg = 'white')
        self.infix.place(x=140, y=70)
        self.infix.focus_set()
        self.postfix = Entry(self.window, width=50, font = ('Helvetica 20',18),
                             bd=30, bg ='gray8', fg='white')
        self.postfix.place(x=200, y=190)
        self.Create_RPN_Calculator_Buttons()

    #Replaces strings with necessary operators
    def GetandReplaceButtons(self):
        try:
            self.expression = self.infix.get()
            self.newtext = self.expression.replace('(', '((')
            self.newtext = self.newtext.replace(')', '))')
            for i in range(0,10):
                self.newtext = self.newtext.replace(str(i), '('+str(i)+')')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.infix.delete(0,END)
            self.infix.insert(0,'MATH - SYNTAX ERROR')
          
    #Create the RPN calculator buttons
    def Create_RPN_Calculator_Buttons(self):
        #ROW1 BUTTONS
        #9,8,6,+,-
        Button(self.window, text = '9', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('9')).place(x=0, y=381)

        Button(self.window, text = '8', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('8')).place(x=90, y=381)

        Button(self.window, text = '7', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('7')).place(x=180, y=381)

        Button(self.window, text = '+', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('+')).place(x=270, y=381)

        Button(self.window, text = '-', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('-')).place(x=360, y=381)

        #ROW2 BUTTONS
        #6,5,4,/,*
        Button(self.window, text = '6', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('6')).place(x=0, y=455)

        Button(self.window, text = '5', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('5')).place(x=90, y=455)

        Button(self.window, text = '4', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('4')).place(x=180, y=455)

        Button(self.window, text = '/', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('/')).place(x=270, y=455)

        Button(self.window, text = '*', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('*')).place(x=360, y=455)

        #ROW3 BUTTONS
        #3,2,1,(,)
        Button(self.window, text = '3', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('3')).place(x=0, y=529)

        Button(self.window, text = '2', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('2')).place(x=90, y=529)

        Button(self.window, text = '1', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('1')).place(x=180, y=529)

        Button(self.window, text = '(', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('(')).place(x=270, y=529)

        Button(self.window, text = ')', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action(')')).place(x=360, y=529)

        #ROW4 BUTTONS
        #0,.,x^n,,,=
        Button(self.window, text = '0', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('0')).place(x=0, y=603)

        Button(self.window, text = ',', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action(',')).place(x=90, y=603)

        Button(self.window, text = 'xⁿ', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.action('^')).place(x=180, y=603)

        Button(self.window, text = 'AC', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.clear()).place(x=270, y=603)

        Button(self.window, text = '=', font=('Helvetica 20',18), width=6, height=2, fg ='white',
               bg ='black', command = lambda: self.execute()).place(x=360, y=603)

        self.window.bind('<Return>',lambda event: self.execute())

    #Add functionality to buttons
    def action(self, argi):
        self.infix.insert(END,argi)

    def clear(self):
        self.infix.delete(0,END)

    #Converts the infix notation into postfix using a stack data structure
    def execute(self):
        self.postfix.delete(0,END)
        try:
            self.GetandReplaceButtons()
            RPN = []
            expressions = self.newtext.split(',')
            for expression in expressions:
                stack = Stack(expression)
                postfix_notation = stack.Convert_to_postfix(expression)
                RPN.append(postfix_notation)
            RPN = str(RPN)
            RPN = RPN.replace('[', '')
            RPN = RPN.replace(']', '')
            RPN = RPN.replace("'", '')
            self.postfix.insert(0, RPN)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.infix.delete(0,END)
            self.infix.insert(0,'MATH - SYNTAX ERROR')


#SUBTASK 4: Create an Encryption Calculator
#- This should be able to encrypt plain-text into cipher-text using shift ciphers
#- In additon, add Vernam cipher encryption
class Encryption_Calculator(UserInterface):
    def __init__(self):
        self.window = window
        self.plaintext = scrolledtext.ScrolledText(self.window, width = 50, height=1, font=('Helvetica 20',18),
                           bd=30, bg = 'gray8', fg = 'white')
        self.plaintext.place(x=130, y=70)
        self.shift = Entry(self.window, width=5, font = ('Helvetica 20',18),
                             bd=30, bg ='gray8', fg='white')
        self.shift.place(x=90,y=190)
        self.key = scrolledtext.ScrolledText(self.window, width = 50, height=1, font=('Helvetica 20',18),
                           bd=30, bg = 'gray8', fg = 'white')
        self.key.place(x=330, y=190)
        self.plaintext.focus_set()
        self.ciphertext = scrolledtext.ScrolledText(self.window, width = 50, height=1, font=('Helvetica 20',18),
                           bd=30, bg = 'gray8', fg = 'white')
        self.ciphertext.place(x=150, y=314)
        self.window.bind('<Return>',lambda event: self.generate())

    #Adding functionality to the text
    
    #This function will convert the plain text to cipher text using a shift cipher
    #This will shift the alphabet by the input amount and replace the text
    def Shift_ciphers(self):
        self.ciphertext.configure(state='normal')
        self.ciphertext.delete('1.0',END)
        try:
            result = ''
            shift = int(eval(self.shift.get()))
            self.newtext = self.plaintext.get('1.0',END)
            self.newtext = self.newtext[0:-1]
            for letter in self.newtext:
                result += chr(ord(letter) + shift)
            self.ciphertext.insert(INSERT, result)
            self.ciphertext.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.ciphertext.delete(0,END)
            self.ciphertext.insert(0,'MATH - SYNTAX ERROR')

    #This function will convert the plaintext and key into binary and XOR operate them
    #Then it converts it to its corresponding location in the unicode table
    def XOR_Encryption(self):
        self.ciphertext.configure(state='normal')
        self.ciphertext.delete('1.0',END)
        try:
            key = str(self.key.get('1.0', END))
            key = key[0:-1]
            self.newtext = self.plaintext.get('1.0',END)
            self.newtext = self.newtext[0:-1]
            binary_key = []
            binary_text = []
            Cipher_text = []
            for i, j in enumerate(self.newtext):
                binary_key.append(bin(ord(key[i])))
                binary_text.append(bin(ord(j)))
            for x, y in enumerate(binary_text):
                Cipher_text.append(bin(eval(binary_key[x]) ^ eval(y)))
            result = [int(eval(i)) for i in Cipher_text]
            self.ciphertext.insert(INSERT, ''.join([chr(i) for i in result]))
            self.ciphertext.configure(state='disabled')
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.ciphertext.delete(0,END)
            self.ciphertext.insert(0,'MATH - SYNTAX ERROR')

    #This function will generate the cipher text into the text entry oon te screen
    #It will do this based on the algoritm used.
    def generate(self):
        try:
            if len(self.shift.get()) == 0:
                self.XOR_Encryption()
            else:
                self.Shift_ciphers()
            self.plaintext.delete('1.0',END)
            self.key.delete('1.0',END)
            self.shift.delete(0,END)
        except (ZeroDivisionError, SyntaxError, ArithmeticError, TypeError, NameError):
            self.ciphertext.delete(0,END)
            self.ciphertext.insert(0,'MATH - SYNTAX ERROR')

#Final Step - Instantiate the UserInterface Class
#Begins running application using Tkinter module
if __name__ == '__main__':
    default_home()
    window.mainloop()
        
        
    
    
