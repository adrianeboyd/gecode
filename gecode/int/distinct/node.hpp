/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Christian Schulte <schulte@gecode.org>
 *
 *  Copyright:
 *     Christian Schulte, 2003
 *
 *  Last modified:
 *     $Date$ by $Author$
 *     $Revision$
 *
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

namespace Gecode { namespace Int { namespace Distinct {

  /*
   * Nodes
   *
   */

  template<class View>
  forceinline
  Node<View>::Node(void) : min(0) {
    // Must be initialized such that the node is considered unvisited initially
  }
  template<class View>
  forceinline Edge<View>*
  Node<View>::edge_fst(void) const {
    return static_cast<Edge<View>*>(BiLink::next());
  }
  template<class View>
  forceinline Edge<View>*
  Node<View>::edge_lst(void) const {
    return static_cast<Edge<View>*>(static_cast<BiLink*>(const_cast<Node<View>*>(this)));
  }
  template<class View>
  forceinline void
  Node<View>::operator delete(void*, size_t) {}
  template<class View>
  forceinline void
  Node<View>::operator delete(void*,Space&) {}
  template<class View>
  forceinline void*
  Node<View>::operator new(size_t s, Space& home) {
    return home.ralloc(s);
  }

  /*
   * Value nodes
   *
   */


  template<class View>
  forceinline
  ValNode<View>::ValNode(int v)
    : _val(v), _matching(NULL) {}
  template<class View>
  forceinline
  ValNode<View>::ValNode(int v, ValNode<View>* n)
    : _val(v), _matching(NULL), _next_val(n) {}
  template<class View>
  forceinline int
  ValNode<View>::val(void) const {
    return _val;
  }
  template<class View>
  forceinline void
  ValNode<View>::matching(Edge<View>* m) {
    _matching = m;
  }
  template<class View>
  forceinline Edge<View>*
  ValNode<View>::matching(void) const {
    return _matching;
  }
  template<class View>
  forceinline ValNode<View>**
  ValNode<View>::next_val_ref(void) {
    return &_next_val;
  }
  template<class View>
  forceinline ValNode<View>*
  ValNode<View>::next_val(void) const {
    return _next_val;
  }
  template<class View>
  forceinline void
  ValNode<View>::next_val(ValNode<View>* n) {
    _next_val = n;
  }



  /*
   * View nodes
   *
   */

  template<class View>
  forceinline
  ViewNode<View>::ViewNode(View x)
    : _view(x) {}
  template<class View>
  forceinline Edge<View>*
  ViewNode<View>::val_edges(void) const {
    return _val_edges;
  }
  template<class View>
  forceinline Edge<View>**
  ViewNode<View>::val_edges_ref(void) {
    return &_val_edges;
  }
  template<class View>
  forceinline View
  ViewNode<View>::view(void) const {
    return _view;
  }

}}}

// STATISTICS: int-prop

