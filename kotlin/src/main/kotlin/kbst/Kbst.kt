package kbst

sealed class Tree {
    object Nil : Tree()
    data class Node(
        val lefty: Tree = Nil,
        val value: Int,
        val righty: Tree = Nil
    ) : Tree()
}

fun Tree.contains(x: Int): Boolean = when (this) {
    Tree.Nil -> false
    is Tree.Node -> if (x < value) {
        lefty.contains(x)
    } else if (value < x) {
        righty.contains(x)
    } else {
        x == value
    }
}

fun Tree.insert(x: Int): Tree = when (this) {
    Tree.Nil -> Tree.Node(Tree.Nil, x, Tree.Nil)
    is Tree.Node -> if (x < value) {
        Tree.Node(lefty.insert(x), value, righty)
    } else if (value < x) {
        Tree.Node(lefty, value, righty.insert(x))
    } else {
        Tree.Node(lefty, x, righty)
    }
}
