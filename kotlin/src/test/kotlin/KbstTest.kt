package kbst

import net.jqwik.api.*
import net.jqwik.api.Arbitraries.*
import net.jqwik.api.Combinators.*
import net.jqwik.api.arbitraries.*
import net.jqwik.kotlin.api.*
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test

class KbstProperties {
    @Provide
    fun trees(): Arbitrary<Tree> = Arbitraries.lazyOf(
        { Arbitraries.of(Tree.Nil) },
        this::nodes
    )

    private fun nodes() =
        combine(trees(), Int.any(0..999), trees(), Tree::Node)

    @Property
    fun `inserted value is contained in tree`(@ForAll("trees") tree: Tree, @ForAll insertValue: Int) {
        assertThat(tree.insert(insertValue).contains(insertValue)).isTrue()
    }
}

class KbstUnitTest {
    @Test fun `tree with a single node 1 contains 1`() {
        val tree = Tree.Node(Tree.Nil, 1, Tree.Nil)
        assertThat(tree.contains(1)).isTrue()
    }

    @Test fun `tree with a single node 1 does not contain 2`() {
        val tree = Tree.Node(Tree.Nil, 1, Tree.Nil)
        assertThat(tree.contains(2)).isFalse()
    }

    @Test fun `a tree contains 1 after 1 is inserted`() {
        val tree = Tree.Nil
        val treeInsert = tree.insert(1)
        assertThat(treeInsert.contains(1)).isTrue()
    }

    @Test fun `a tree contains 1 after 1 and 2 are inserted`() {
        val tree = Tree.Nil
        val treeInsert = tree.insert(1).insert(2)
        assertThat(treeInsert.contains(1)).isTrue()
        assertThat(treeInsert.contains(2)).isTrue()
    }
}
