/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Guido Tack <tack@gecode.org>
 *     Adriane Boyd <adriane@ling.ohio-state.edu>
 *
 *  Copyright:
 *     Guido Tack, Adriane Boyd, 2010
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

#include <iostream>
#include <fstream>
#include <gecode/flatzinc.hh>
#include <gecode/flatzinc/parser.hh>

using namespace std;
using namespace Gecode;

struct FlatZincSpaceInfo {
  FlatZinc::FlatZincSpace* fg;
  FlatZinc::Printer& p;
  FlatZinc::FlatZincQuickxplainOptions& opt;
  Support::Timer& t_total;
  bool debug;
};

set<int> getConflicts(FlatZincSpaceInfo* s, set<int> fgc);
set<int> quickxplain(FlatZincSpaceInfo* s, set<int> bgc, set<int> fgc);
bool runSpace(FlatZincSpaceInfo* s, set<int> c);
int findFirstFailure(FlatZincSpaceInfo* s, set<int> bgc, 
                              set<int> fgc);
int failureSearch(FlatZincSpaceInfo* s, FlatZinc::FlatZincSpace* fg,
                           FlatZinc::FlatZincSpace* fg0, set<int>* c,
                           int lo, int hi);
void printSet(set<int> s);

int main(int argc, char** argv) {
  
  Support::Timer t_total;
  t_total.start();
  FlatZinc::FlatZincQuickxplainOptions opt("Gecode/FlatZinc QuickXplain");
  opt.parse(argc, argv);

  if (argc!=2) {
    cerr << "Usage: " << argv[0] << " [options] <file>" << endl;
    cerr << "       " << argv[0] << " -help for more information" << endl;
    exit(EXIT_FAILURE);
  }
  
  const char* filename = argv[1];
  opt.name(filename);
  
  FlatZinc::Printer p;
  FlatZinc::FlatZincSpace* fg = NULL;
  if (!strcmp(filename, "-")) {
    fg = FlatZinc::parse(cin, p, std::cerr, NULL, false);
  } else {
    fg = FlatZinc::parse(filename, p, std::cerr, NULL, false);
  }

  if (fg) {
    // add all constraints to the foreground
    // (if required, you can easily replace this with your 
    // own method that identifies constraints that are never 
    // part of a conflict and posts them at this point)
    //   set<int> bgc, fgc;
    //   preprocessConstraints(fg, &bgc, &fgc);
    //   fg->postStoredConstraints(bgc);
    //   fg->deleteStoredConstraints(bgc);
    set<int> fgc;
    for (int i = 0; i < fg->constraintCount; i++) {
      fgc.insert(i);
    }

    fg->createBranchers(fg->solveAnnotations(), false, std::cerr);

    // find and print out conflicts
    FlatZincSpaceInfo s = {fg, p, opt, t_total, false}; // change to true
                                                        // for debugging info
    set<int> conflicts = getConflicts(&s, fgc);

    if (conflicts.size() > 0) {
      cout << "Constraints in the input have been numbered sequentially starting at 0." << endl;
      cout << "Conflicts found by QuickXplain: ";
      printSet(conflicts);
    } else {
      cout << "No conflicts!" << endl;
    }
  } else {
    exit(EXIT_FAILURE);    
  }
  delete fg;
  
  return 0;
}

/**
 * Wrapper for quickxplain().
 *
 */
set<int> getConflicts(FlatZincSpaceInfo *s, set<int> fgc) {
  set<int> emptySet, conflicts;

  // if no conflicts, return
  if (runSpace(s, fgc)) {
    return emptySet;
  }
  conflicts = quickxplain(s, emptySet, fgc);
  return conflicts;
}

/**
 * QUICKXPLAIN algorithm from Junker (2004):
 *
 * Ulrich Junker, 2004. QUICKXPLAIN: Preferred Explanations and 
 * Relaxations for Over-Constrained Problems. AAAI 2004: 167-172.
 *
 */
set<int> quickxplain(FlatZincSpaceInfo* s, set<int> bgc, set<int> fgc) {
  set<int> emptySet;

  // check that the background is satisfiable
  if (!runSpace(s, bgc)) {
    return emptySet;
  }

  // check that the current foreground is not empty
  // if so, something has gone wrong
  if (fgc.empty()) {
    exit(EXIT_FAILURE);
  }

  // find k where bgc + fgc[1 - (k-1)] is satisfiable and 
  // bgc + fgc[1 - k] is not
  unsigned int k = findFirstFailure(s, bgc, fgc);

  // split the constraints fgc[1 - (k-1)] into two halves, u1 and u2
  unsigned int split = k / 2;

  set<int>::iterator it;
  set<int> u1, u2, x;
  it = fgc.begin();
  for (unsigned int i = 0; i < k; i++) {
    if (i <= split) {
      u1.insert(*it);
    } else {
      u2.insert(*it);
    }

    it++;
  }

  // add the kth constraint to the current set of conflicts
  x.insert(*it);
  int k_x = *it;

  set<int> delta1, delta2;

  // check for conflicts in u2
  if (u2.size() > 0) {
    // create background for u2
    set<int> bgi;
    bgi.insert(bgc.begin(), bgc.end());
    it = fgc.begin();
    for (unsigned int i = 0; i <=split; i++) {
      bgi.insert(*it);
      it++;
    }
    bgi.insert(k_x);

    delta2 = quickxplain(s, bgi, u2);
    x.insert(delta2.begin(), delta2.end());
  }

  // check for conflicts in u1
  if (u1.size() > 0) {
    // create background for u1
    set<int> bg0;
    bg0.insert(bgc.begin(), bgc.end());
    bg0.insert(x.begin(), x.end());
    delta1 = quickxplain(s, bg0, u1);
    x.insert(delta1.begin(), delta1.end());
  }

  // return the current set of known conflicts
  return x;
}

/**
 * Return whether the space is not failed with the given constraints.
 *
 */
bool runSpace(FlatZincSpaceInfo* s, set<int> c) {
  // create a clone of fg to work on and post constraints
  FlatZinc::FlatZincSpace* fg = (FlatZinc::FlatZincSpace*) s->fg->clone();
  fg->postStoredConstraints(c);

  bool ret = false;

  if (s->debug) {
    cout << "Running with # constraints: " << c.size() << endl;
  }

  ret = fg->isSatisfiable(s->opt);

  if (s->debug) {
    cout << "Status: " << fg->status() << endl;
    cout << "Satisfiable: " << ret << endl;
    cout << endl;
  }

  delete fg;

  return ret;
}

/**
 * Wrapper that posts background constraints and sets up variables
 * needed for failureSearch().
 *
 */
int findFirstFailure(FlatZincSpaceInfo* s, set<int> bgc, set<int> fgc) {
  // create a clone for the search to use as a reference
  FlatZinc::FlatZincSpace* fg = (FlatZinc::FlatZincSpace*) s->fg->clone();

  // post bg constraints to the reference clone
  set<int>::iterator it = bgc.begin();
  while (it != bgc.end()) {
    fg->postStoredConstraint(*it);
    it++;
  }
  fg->status();

  // create a clone of the reference clone for the search to modify
  FlatZinc::FlatZincSpace* fg2 = (FlatZinc::FlatZincSpace*) fg->clone();

  int k = failureSearch(s, fg2, fg, &fgc, 0, fgc.size() - 1);

  if (s->debug) {
    cout << "Failed at k: " << k << endl;
    cout << endl;
  }
  
  delete fg;
  delete fg2;

  return k;
}

/**
 * A recursive binary search for the constraint index in c at which
 * space fg with constraints c[0..k-1] is satisfiable but with 
 * constraints c[0..k] is not.
 *
 */
int failureSearch(FlatZincSpaceInfo* s, FlatZinc::FlatZincSpace* fg, 
                           FlatZinc::FlatZincSpace* fg0, set<int>* c, 
                           int lo, int hi) {

  if (s->debug) {
    cout << "Searching for k between: " << lo << "/" << hi << endl;
  }

  if (lo == hi) {
    return lo;
  }

  // the space should fail at some point,
  // so this should never happen
  if (hi < lo) {
    cerr << "Problem finding failed constraint." << endl;
    exit(EXIT_FAILURE);
  }

  // at this point c[0..lo-1] are already posted
  
  // find the midpoint
  int mi = lo + ((hi - lo) / 2);

  // post c[lo..mi-1] in fg
  set<int>::iterator it = c->begin();
  advance(it, lo);
  for (int i = lo; i <= mi; i++) {
    fg->postStoredConstraint(*it);
    it++;
  }

  if (fg->isSatisfiable(s->opt)) {
    // continue to use fg since we are only adding constraints
    return failureSearch(s, fg, fg0, c, mi + 1, hi);
  }

  // clone fg0 in order to create a space with c[0..lo-1] posted
  FlatZinc::FlatZincSpace* fg2 = (FlatZinc::FlatZincSpace*) fg0->clone();

  it = c->begin();
  for (int i = 0; i < lo; i++) {
    fg2->postStoredConstraint(*it);
    it++;
  }

  int ret = failureSearch(s, fg2, fg0, c, lo, mi);

  delete fg2;

  return ret;
}

void printSet(set<int> s) {
  set<int>::iterator it;
  for (it = s.begin(); it != s.end(); it++) {
    cout << *it << " ";
  }
  cout << endl;
}

// STATISTICS: flatzinc-any
