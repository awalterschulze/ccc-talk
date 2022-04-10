/*
Run using:
    kotlinc -script BST.kts
*/

sealed class Tree {
    object Nil : Tree() {}
    data class Node(
        val lefty: Tree = Nil,
        val value: Int,
        val righty: Tree = Nil
    ) : Tree()
}

fun Tree.contains(x: Int) : Boolean = when (this) {
    Tree.Nil -> false
    is Tree.Node -> if (x < value) {
        lefty.contains(x)
    } else if (value < x) {
        righty.contains(x)
    } else {
        x == value
    }
}

val tree1 = Tree.Node(Tree.Nil, 1, Tree.Nil)

require(tree1.contains(1))
require(!tree1.contains(2))

val tree2 = Tree.Node(tree1, 2, Tree.Node(Tree.Nil, 3, Tree.Nil))

require(tree2.contains(1))
require(tree2.contains(2))
require(tree2.contains(3))
require(!tree2.contains(4))

fun Tree.insert(x: Int) : Tree = when (this) {
    Tree.Nil -> Tree.Node(Tree.Nil, x, Tree.Nil)
    is Tree.Node -> if (x < value) {
        Tree.Node(lefty.insert(x), value, righty)
    } else if (value < x) {
        Tree.Node(lefty, value, righty.insert(x))
    } else {
        Tree.Node(lefty, x, righty)
    }
}

require(tree1.insert(2).contains(2))
require(tree1.insert(0).contains(0))
require(tree1.insert(2).contains(1))
require(!tree1.insert(2).contains(3))
