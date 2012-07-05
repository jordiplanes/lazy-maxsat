/*
 * Code been developed in Universitat de Lleida / CCIA
 * 
 * Created to solve Weighted MAX-SAT CNF instances.
 * Usage: maxsat <file.cnf> <upper-bound>
 *
 * Creation date: Oct 18th, 2004
 *
 * To do: recursive -> iterative
 *
 */

#include <cstdio>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <iterator>
//#include <vector>

#include "stack.h"
#include "vector.h"

using namespace std;


extern "C" {
  int local_search( char* );
}

/*
 * GLOBAL FLAGS
 */

//#define DEBUG_ON
//#define MODE_TEST

#define RANDOM_ACCESS

/*
 * ALGORITHM FLAGS
 */

//#define LOCAL_SEARCH
//#define UNIT_PROPAGATION
#define UNIT_CLAUSE_ELIMINATION
#define VAR_MAPPING
#define LOOK_AHEAD
#define NEIGHBOURS
#define BACKBONE

//#define STAR_RULE_IR
//#define LB4 // Incompatible with UP_LOOK_AHEAD
//#define CUC_RULE
//#define UP_LOOK_AHEAD
//#define DUC_RULE
//#define STAR_RULE
//#define RESOLUTION_RULE
//#define MANUAL_ORDERING
//#define ONLY_2SAT

/*
 * CONSTANTS
 */

#define MAX_LINE 10000
#define MAX_VARS 4000
#define MAX_CLAUSES 200000
#define MAX_LENGTH 1000
#define MAX_UNIT 350
#define FALSE 0
#define TRUE 1
#define UNDEF -1

/*
 * TYPES
 */

//typedef pair<int,int> UnaryWeightedClause;

struct UnaryWeightedClause {
  int first, second;
  UnaryWeightedClause( int f = 0, int s = 0 ) { first = f; second = s; }
  UnaryWeightedClause( const UnaryWeightedClause& u ) { first = u.first; second = u.second; }
  bool operator==( const UnaryWeightedClause& u ) { return first == u.first; }
  bool operator!=( const UnaryWeightedClause& u ) { return first != u.first; }
};

typedef vector<UnaryWeightedClause,MAX_UNIT> BinaryClauseList;

struct Clause {
  int *literals;//[MAX_LENGTH];
  int weight;
  int length;
  int max_value; // +/- variable
  int max_value_abs;
  int max_value_abs_2;
  int max_literal;
  int max_index; // position
  int penultimate_value; // +/- variable
  int penultimate_value_abs;
  int penultimate_literal; // true or false
  int penultimate_index; // position
  int apn_value;
  int apn_value_abs;
  int apn_literal;
  int apn_index;
  Clause& operator=( const Clause& );
} clauses[MAX_CLAUSES];

BinaryClauseList clausesbc[ 2*MAX_VARS ];

struct Variable {
  int count;
  int literal_count[2];
  int neighbours[ 2 ][ MAX_VARS ];
  int weight;
} variables[ MAX_VARS ];

int unit_value[ MAX_VARS ];
int var_map[ MAX_VARS ];
int num_vars, num_clauses;
int num_long_clauses;
int last_var;
int ub;
int solution[ MAX_VARS ];
int partial_solution[ MAX_VARS ];
int unit_clauses[ 2 * MAX_VARS ], unit_clauses_pre[ 2 * MAX_VARS ];
int backtracks;
#ifdef MODE_TEST
int stop_point;
#endif
int min_weight = INT_MAX, max_weight = 1, total_weight = 0;
stack<UnaryWeightedClause,MAX_CLAUSES> unit_stack;
stack<int,MAX_CLAUSES> added_binary_clauses;
stack<int,MAX_VARS> added_binary_clauses_index;

#ifdef STAR_RULE_IR
stack<int,MAX_CLAUSES> binary_stack_new;
stack<int,MAX_CLAUSES> binary_stack_min_weight;
stack<int*,MAX_CLAUSES> binary_stack_unit_pointer;
#endif

#ifdef RESOLUTION_RULE
#include <list>

struct ResolutionInfo {
  int first, second, weight;
  ResolutionInfo( int f=0, int s=0, int w=0 ) { first = f; second = s; weight = w; }
  ResolutionInfo( int var, const UnaryWeightedClause& uwc ) {
    first = var;
    second = uwc.first;
    weight = uwc.second;
  }    
};
typedef list<ResolutionInfo> ResolutionList;
typedef list<UnaryWeightedClause> UnaryList;

ResolutionList *resolution_list;
UnaryList *unit_resolution_list;
#endif

// Simple inline functions

inline int make_literal( int var ) {
  return var < 0 ? FALSE : TRUE;
}

inline int make_offset( int literal ) {
  return 2*abs( literal ) + make_literal( literal );
}

inline int unmake_offset( int offset ) {
  return offset/2 * (offset%2 == FALSE ? -1 : 1 );
}

inline int make_complementary( int offset ) {
  return (offset % 2) == 0 ? offset+1 : offset-1; 
}

// Operators

Clause& Clause::operator=( const Clause& s ) {
  length = s.length;
  literals = new int[ length ];
  for( int i = 0; i < length; i++ ) {
    literals[ i ] = s.literals[ i ];
  }
  weight = s.weight;
  max_value = s.max_value;
  max_value_abs = s.max_value_abs;
  max_value_abs_2 = s.max_value_abs_2;
  max_literal = s.max_literal;
  max_index = s.max_index;
  penultimate_value = s.penultimate_value;
  penultimate_value_abs = s.penultimate_value_abs;
  penultimate_literal = s.penultimate_literal;
  penultimate_index = s.penultimate_index;
  apn_value = s.apn_value;
  apn_value_abs = s.apn_value_abs;
  apn_literal = s.apn_literal;
  apn_index = s.apn_index;
  return *this;
}

bool operator<( Clause begin, Clause end ) {
  return begin.apn_value_abs < end.apn_value_abs;
}

bool variable_ordering( int begin, int end ) {
#ifdef VAR_MAPPING
#ifdef NEIGHBOURS
  if ( variables[ begin ].count == variables[ end ].count ) {
    return variables[ begin ].weight < variables[ end ].weight;
  }
#endif
  return variables[ begin ].count > variables[ end ].count;
#else
  return variables[ end ].count == 0;
#endif
}

// Printings
//#ifdef DEBUG_ON
template <class Iterator>
ostream& print_list( ostream& os, const Iterator begin, const Iterator end, char separator ) {
  for( Iterator iter = begin; iter != end; iter++ ) {
    os << "[" << iter - begin << "]" << *iter << separator;
  }
  return os;
}

ostream& operator<<( ostream& os, const Clause& c ) {
  os << "{" << c.weight << "}";
  copy( c.literals, c.literals + c.length, ostream_iterator<int>(os, " ") );
  os << "(" << c.max_value << "," << c.max_index << ")";
  os << "(" << c.penultimate_value << "," << c.penultimate_index << ")";
  os << "(" << c.apn_value << "," << c.apn_index << ")";
  return os;
}

ostream& operator<<( ostream& os, const UnaryWeightedClause& uwc ) {
  os << "@" << &uwc << "(" << uwc.first << " [" << uwc.second << "])";
  return os;
}

ostream& operator<<( ostream& os, BinaryClauseList& bcl) {
  for( BinaryClauseList::iterator i = bcl.begin(); i != bcl.end(); i++ ) {
    os << "[" << i - bcl.begin() << "]" << *i << " ";
  }
  return os;
}

ostream& operator<<( ostream& os, const Variable& v ) {
  os << "(" << "c=" << v.count << " w=" << v.weight << ")";
  return os;
}
#ifdef RESOLUTION_RULE
ostream& operator<<( ostream& os, const ResolutionInfo& ri ) {
  os << ri.first << ri.second << ri.weight << endl;
  return os;
}
#endif
//#endif
// Debuging

void critical_error( string message ) {
#ifdef DEBUG_ON
  cout << "Clauses" << endl;
  cout << print_list( cout, clausesbc, clausesbc + (2*num_vars+2), '\n' );
#endif
  cerr << "Error: " << message << endl;
  exit(-1);
}

void check_runtime_error() {
  int max_counter = 0, counter = 0, var = abs( clauses[ 0 ].penultimate_value );
  for(int i = 1; i < num_long_clauses; i++ ) {
    while( abs( clauses[ i ].penultimate_value ) == var ) {
      counter++;
      i++;
    }
    max_counter = max( counter, max_counter );
    counter = 0;
    var = abs( clauses[ i ].penultimate_value );
  }
  if ( max_counter > MAX_UNIT-1 ) {
    cout << "Max: " << max_counter << endl;
    critical_error( "Error in MAX_UNIT" );
  }
}

// B&B Algorithm functions

void readfile(char *filename ) {
  ifstream ifs ( filename );
  char line[ MAX_LINE ];
  char strtmp[ 5 ];
  int literals[ MAX_LENGTH ];

  do {
    ifs.getline( line, MAX_LINE );
  } while ( line[0] == 'c' );

  sscanf( line, "p %s %d %d", strtmp, &num_vars, &num_clauses );
  
  cout << "c Num vars: " << num_vars << " Num clauses: " << num_clauses << endl;

  for( int i = 1; i <= num_vars; i++ ) {
    var_map[ i ] = i;
    variables[ i ].count = 0;
    variables[ i ].literal_count[ TRUE ] = 0;
    variables[ i ].literal_count[ FALSE ] = 0;
    unit_value[ i ] = UNDEF;
    unit_clauses_pre[ 2*i ] = unit_clauses_pre[ 2*i + 1 ] = 0;
  }

#ifdef MODE_TEST
    int max_length = 1
#ifdef UNIT_CLAUSE_ELIMINATION
      , num_uc = 0
#endif
;
#endif

    int weight;
  for( int i = 0, j, k; i < num_clauses; i++ ) {
    ifs >> weight;    
    clauses[i].weight = weight;
    total_weight += weight;
    max_weight = max( max_weight, weight );
    min_weight = min( min_weight, weight );
    ifs >> k;
    for(j = 0; k != 0; j++) {
      variables[ abs(k) ].count += clauses[i].weight;
      variables[ abs(k) ].literal_count[ make_literal(k) ] += clauses[i].weight;
      literals[j] = k;
      ifs >> k;
    }    
    clauses[i].length = j;
    clauses[i].literals = new int[ j ];
    memcpy( clauses[i].literals, literals, j*sizeof(int) );

#ifdef MODE_TEST
    max_length = max( max_length, j );
#endif
   
#ifdef UNIT_CLAUSE_ELIMINATION
    if ( clauses[i].length == 1 ) {
      int& literal = clauses[i].literals[0];
#ifdef DEBUG_ON
      cout << "Unary clause " << literal << " removed" << endl;
#endif
#ifdef MODE_TEST
      num_uc++;
#endif
      unit_clauses_pre[ make_offset( literal ) ] = clauses[ i ].weight;
      variables[ abs( literal ) ].count -= clauses[i].weight;
      variables[ abs(k) ].literal_count[ make_literal(k) ] -= clauses[i].weight;
      i--;
      num_clauses--;
    }
#endif
  }

#ifdef MODE_TEST
  if ( !ifs.good() ) {
    critical_error( "Error reading the file" );
  }
#ifdef UNIT_CLAUSE_ELIMINATION
  cout << "Unary clauses removed: " << num_uc << endl;
  if ( num_uc >= MAX_UNIT ) {
    critical_error( "MAX_UNIT exceeded" );
  }
#endif
  cout << "Max clause length " << max_length << endl;
  if ( max_length >= MAX_LENGTH ) {
    critical_error( "MAX_LENGTH exceeded" );
  }
#endif
}

void neighbours_ordering() {
  int var_j;

  for( int i = 1; i <= num_vars; i++ ) {
    for( int j = 1; j <= num_vars; j++ ) {
      variables[ i ].neighbours[ TRUE ][ j ] = 0;
      variables[ i ].neighbours[ FALSE ][ j ] = 0;
    }
  }
  for( int i = 0; i < num_clauses; i++ ) {
    for( int j = 0; j < clauses[i].length; j++ ) {
      var_j = abs( clauses[i].literals[j] );
      for( int k = 0; k < clauses[i].length; k++ ) {
	if ( j != k ) {
	  variables[ var_j ].neighbours[ make_literal(clauses[i].literals[ k ]) ]
	    [ abs( clauses[ i ].literals[ k ] ) ]++;
	}
      }
    }
  }
  for( int i = 1; i <= num_vars; i++ ) {
    for( int j = 1; j <= num_vars; j++ ) {     
#ifdef BACKBONE
      variables[ i ].weight +=
      	(variables[ i ].neighbours[ TRUE ][ j ] * variables[ j ].literal_count[ TRUE ] )
      	+ (variables[ i ].neighbours[ FALSE ][ j ] * variables[ j ].literal_count[ FALSE ]);
#else
      variables[ i ].weight += 
	(variables[ i ].neighbours[ TRUE ][ j ] + variables[ i ].neighbours[ FALSE ][ j ])
      	* variables[ j ].count;
#endif
    }
  }
}

void var_mapping( int mapping[ MAX_VARS ] ) {
  int i;

  for( i = 1; i <= num_vars; i++ ) {
    mapping[ i ] = find( var_map + 1, var_map + num_vars + 1, i ) - var_map;
  }
  for( i = 0; i < num_clauses; i++ ) {
    for( int j = 0; j < clauses[i].length; j++ ) {
      clauses[ i ].literals[ j ] = clauses[ i ].literals[ j ] > 0 ? 
	mapping[ clauses[ i ].literals[ j ] ] : -mapping[ -clauses[ i ].literals[ j ] ];
    }
  }
  for( i = 1; i <= num_vars; i++ ) {
    unit_clauses[ 2*mapping[ i ] ] = unit_clauses_pre[ 2*i ];
    unit_clauses[ 2*mapping[i] + 1 ] = unit_clauses_pre[ 2*i + 1 ];
  }
}

// Clause DB functions
#ifdef RESOLUTION_RULE
inline bool pair_marked( const UnaryWeightedClause& p ) {
  return p.first == 0;
}

inline void mark_pair( UnaryWeightedClause& p ) {
  p.first = 0;
}

inline void literal_cleaning( const int var ) {
  clausesbc[var].erase( remove_if( clausesbc[var].begin(), clausesbc[var].end(), pair_marked ), 
			clausesbc[var].end() );
}
#endif

BinaryClauseList::iterator find( BinaryClauseList::iterator i, 
				 const BinaryClauseList::iterator& end, 
				 int var ) {
  while( i != end and i->first != var ) i++;
  return i;
}

BinaryClauseList::iterator find( BinaryClauseList::iterator i, 
				 const BinaryClauseList::iterator& end, 
				 UnaryWeightedClause uwc ) {
  while( i != end and *i != uwc ) i++;
  return i;
}

void add_clause_db( int penultimate, int last, int weight ) {
#ifdef DEBUG_ON
  cout << "Add clause " << penultimate << " " << last << " " << weight << endl;
#endif
#ifdef MODE_TEST
  if ( weight == 0 ) {
    critical_error( "zero weight");
  }
#endif
#ifdef RANDOM_ACCESS
    clausesbc[ penultimate ].push_back( UnaryWeightedClause( last, weight ) );
#else
    clausesbc[ penultimate ].push_front( UnaryWeightedClause( last, weight ) );
#endif
}

bool null_clause( Clause c ) {
  return c.penultimate_value == 0;
}

void set_null_clause( Clause& c ) {
  c.penultimate_value = 0;
}

void create_binary_clause_db() {
  //UnaryWeightedClause bwc;
  for( int c = 0; c < num_clauses; c++ ) {
    if ( clauses[c].length == 2 ) {
#ifdef DEBUG_ON
      cout << "Adding " << make_offset( clauses[c].penultimate_value ) << " " << 
	make_offset( clauses[c].max_value ) << endl;
#endif
      add_clause_db( make_offset( clauses[ c ].penultimate_value ),
		     make_offset( clauses[ c ].max_value ), clauses[ c ].weight );
      set_null_clause( clauses[ c ] );
    }    
  }
  Clause* last_clause = remove_if( &clauses[0], &clauses[num_clauses], null_clause );
  num_long_clauses = last_clause - clauses;
#ifdef DEBUG_ON
  cout << "Num long clauses " << num_long_clauses  << endl;
#endif
  last_var = num_vars; //clauses[ num_clauses-1 ].penultimate_value_abs;
}

void update_clause_max_value() {
  int l;

  for( int c = 0; c < num_clauses; c++ ) {
    
    clauses[ c ].max_index = 0;
    clauses[ c ].max_value = clauses[ c ].literals[ 0 ];
    for( l = 1; l < clauses[c].length; l++ ) {
      if ( abs( clauses[ c ].literals[ l ] ) > abs( clauses[ c ].max_value ) ) {
	clauses[ c ].max_value = clauses[ c ].literals[ l ];
	clauses[ c ].max_index = l;
      }
    }
    clauses[ c ].max_value_abs = abs( clauses[ c ].max_value );
    clauses[ c ].max_value_abs_2 = 2*abs( clauses[ c ].max_value );
    clauses[ c ].max_literal = make_literal( clauses[ c ].max_value );
    
    l = clauses[ c ].max_index == 0 ? 1 : 0;
    clauses[ c ].penultimate_index = l;
    clauses[ c ].penultimate_value = clauses[ c ].literals[ l ];

    for( ; l < clauses[c].length; l++ ) {
      if ( abs( clauses[ c ].literals[ l ] ) > abs( clauses[ c ].penultimate_value )
	   && l != clauses[ c ].max_index ) {
	clauses[ c ].penultimate_value = clauses[ c ].literals[ l ];
	clauses[ c ].penultimate_index = l;
      }
    }
    clauses[ c ].penultimate_value_abs = abs( clauses[ c ].penultimate_value );
    clauses[ c ].penultimate_literal = make_literal( clauses[ c ].penultimate_value );

    if( clauses[ c ].length > 2 ) {
      clauses[ c ].apn_index = 0;
      while( clauses[ c ].apn_index == clauses[ c ].max_index 
	     || clauses[ c ].apn_index == clauses[ c ].penultimate_index ) {
	clauses[ c ].apn_index++;
      }
      clauses[ c ].apn_value = clauses[ c ].literals[ clauses[ c ].apn_index ];
      l = clauses[ c ].apn_index+1;
      while( l < clauses[ c ].length ) {
	if( abs( clauses[ c ].apn_value ) < abs( clauses[ c ].literals[ l ] )
	    && l != clauses[ c ].max_index 
	    && l != clauses[ c ].penultimate_index ) {
	  clauses[ c ].apn_value = clauses[ c ].literals[ l ];
	  clauses[ c ].apn_index = l;	  
	}
	l++;
      }
      clauses[ c ].apn_value_abs = abs( clauses[ c ].apn_value );
      clauses[ c ].apn_literal = make_literal( clauses[ c ].apn_value );
    }
  }
}

bool clause_is_unsat( Clause& clause ) {
  for( int i = 0; i < clause.length; i++ ) {
    if ( i != clause.max_index && i != clause.penultimate_index && i != clause.apn_index ) {
      if ( partial_solution[ abs( clause.literals[ i ] ) ] ==
	   make_literal( clause.literals[ i ] ) )
	return false;
    }
  }      
  return true;
}

int weight_count( BinaryClauseList bcl ) {
  int weight = 0;
  for( BinaryClauseList::iterator i = bcl.begin(); i < bcl.end(); i++ ) {
    weight += i->second;
  }
  return weight;
}

int weight_literals( BinaryClauseList::iterator begin, BinaryClauseList::iterator end, 
		   int offset ) {
  int weight = 0;
  for( BinaryClauseList::iterator i = begin; i != end; i++ ) {
    if ( i->first == offset ) weight += i->second;
  }
  return weight;
}

void check_clauses_bc( int var, int index_clause, int length[ 2 ] ) { //!!
  /* Counting 2-SAT */
  length[ TRUE ] = weight_count( clausesbc[ make_offset( var ) ] );
  length[ FALSE] = weight_count( clausesbc[ make_offset( -var )] );
  if ( num_long_clauses > 0 ) {
  //#ifndef ONLY_2SAT  
  /* Counting 3-SAT */
  while( clauses[ index_clause ].apn_value_abs < var && index_clause < num_clauses ) {
    if( clauses[ index_clause ].max_value_abs == var ) {
      length[ clauses[ index_clause ].max_literal ] += clauses[ index_clause ].weight;
    }
    else if ( clauses[ index_clause ].penultimate_value_abs == var &&
              clauses[ index_clause ].max_literal !=
              partial_solution[ clauses[ index_clause ].max_value_abs ] ) {
      length[ clauses[ index_clause ].penultimate_literal ] += clauses[ index_clause ].weight;
    }
    index_clause++;
  }
  for( ; clauses[ index_clause ].apn_value_abs == var; index_clause++ ) {
    length[ clauses[ index_clause ].apn_literal ] += clauses[ index_clause ].weight;
  }
  //#endif
  }
}

void add_unit_clauses_bc( int literal ) {
  for( BinaryClauseList::iterator i = clausesbc[ literal ].begin(); 
       i != clausesbc[ literal ].end(); i++ ) {
    unit_clauses[ i->first ] += i->second;
  }
}

void remove_unit_clauses_bc( int literal ) {
  for( BinaryClauseList::iterator i = clausesbc[ literal ].begin(); 
       i != clausesbc[ literal ].end(); i++ ) {
    unit_clauses[ i->first ] -=  i->second;
  }
}

bool unit_propagation( int var ) {
  while( var <= num_vars ) {
    if ( unit_clauses[ make_offset( var ) ] >= min_weight && 
	 unit_clauses[ make_offset( -var ) ] >= min_weight ) {
      return true;
    }
    if ( unit_clauses[ make_offset( -var )  ] >= min_weight ) {
      unit_value[ var++ ] = FALSE;
    }
    else if ( unit_clauses[ make_offset( var ) ] >= min_weight ) {
      unit_value[ var++ ] = TRUE;
    }
    else return false;
  }
  return false;
}

void undo_unit_propagation( int var ) {
  while( unit_value[ var ] != UNDEF && var <= num_vars ) {
    unit_value[ var++ ] = UNDEF;
  }
}

#ifdef RESOLUTION_RULE

inline void add_resolution( int var, int var1, const UnaryWeightedClause& var2 ) {
#ifdef DEBUG_ON
  cout << "Add resolution [" << var << "]" << var1 << " " << var2.first << " (" << var2.second << ")" << endl;
#endif
#ifdef MODE_TEST
  if ( var2.second == 0 ) {
    critical_error( "nil resolution");
  }
#endif
  resolution_list[ var ].push_back( ResolutionInfo( var1, var2 ) );
}

inline void add_unit_resolution( int var, int unit, int weight ) {
#ifdef DEBUG_ON
  cout << "Add unit resolution " << unmake_offset( unit ) << " (" << weight << ")" << endl;
#endif
  unit_clauses[ unit ] += weight;
  unit_resolution_list[ var ].push_back( UnaryWeightedClause( unit, weight ) );
#ifdef MODE_TEST
  if ( weight == 0 ) {
    critical_error( "nil unit resolution");
  }
#endif
}

void remove_resolutions( int var ) {
  ResolutionList::iterator i = resolution_list[ var ].begin(),
    end = resolution_list[ var ].end();
  for( ; i != end; i++ ) {
#ifdef DEBUG_ON
    cout << "Remove resolution [" << var << "]" << i->first << " " << i->second << "(" << i->weight << ")" << endl;
#endif   
    add_clause_db( i->first, i->second, i->weight );
  }
  resolution_list[ var ].clear();
  UnaryList::iterator j = unit_resolution_list[ var ].begin(),
    end2 = unit_resolution_list[ var ].end();
  for( ; j != end2; j++ ) {
    unit_clauses[ j->first ] -= j->second;
#ifdef DEBUG_ON
    cout << "Remove unit resolution " << unmake_offset( j->first ) << " (" << j->second << ")" << endl;
#endif
#ifdef MODE_TEST
    if ( unit_clauses[ j->first ] < 0 ) {
      critical_error("Unit clauses negative");
    }
#endif
  }
  unit_resolution_list[ var ].clear();
}

void apply_var_resolution( int v, int var_p, int var_n, BinaryClauseList::iterator& begin_p, 
		       BinaryClauseList::iterator& found_n ) {
  //cout << "begin_p " << *begin_p << endl;
  //cout << "found_n " << *found_n << endl;
  if( begin_p->second > found_n->second ) {	
    //cout << "First with var " << var << endl;
    add_unit_resolution( v, found_n->first, found_n->second );
    add_resolution( v, var_n, *found_n );
    add_resolution( v, var_p, UnaryWeightedClause( begin_p->first, found_n->second ) );
    begin_p->second -= found_n->second;
    mark_pair( *found_n );
  }
  else {
    //cout << "Second with var " << var << endl;
    add_unit_resolution( v, begin_p->first, begin_p->second );
    add_resolution( v, var_p, *begin_p );
    add_resolution( v, var_n, UnaryWeightedClause( found_n->first, begin_p->second ) );
    if ( found_n->second != begin_p->second ) {
      found_n->second -= begin_p->second;
    }
    else {
      mark_pair( *found_n );
    }
    mark_pair( *begin_p );
  }
}

void resolution_in_var( const int v, const int var ) { 
  BinaryClauseList::iterator begin_p = clausesbc[ make_offset( var ) ]. begin(),
    end_p = clausesbc[ make_offset( var ) ].end();
  BinaryClauseList::iterator begin_n = clausesbc[ make_offset( -var ) ]. begin(),
    end_n = clausesbc[ make_offset( -var ) ].end();
#ifdef DEBUG_ON
  cout << "Resolution in var " << var << endl;
  cout << "+var: ";
  for( BinaryClauseList::iterator i = begin_p; i != end_p; i++ ) {
    cout << " (" << i-begin_p << ") " << *i;
  } cout << endl;
  cout << "-var: ";
  for( BinaryClauseList::iterator i = begin_n; i != end_n; i++ ) {
    cout << " (" << i-begin_n << ") " << *i;
  } cout << endl;
#endif
  while( begin_p != end_p ) {
    BinaryClauseList::iterator found_n = find( begin_n, end_n, begin_p->first );
    if ( found_n != end_n ) {
      apply_var_resolution( v, make_offset( var ), make_offset( -var ), begin_p, found_n );
    }
    do {
      begin_p++; 
    } while( begin_p != end_p and pair_marked( *begin_p ) );
  }
  literal_cleaning( make_offset( var ) );
  literal_cleaning( make_offset( -var ) );
}

void apply_literal_resolution( int v, int var_offset, BinaryClauseList::iterator& begin, 
		       BinaryClauseList::iterator& found ) {
  if( begin->second > found->second ) {	
    add_unit_resolution( v, var_offset, found->second );
    add_resolution( v, var_offset, *found );
    add_resolution( v, var_offset, UnaryWeightedClause( begin->first, found->second ) );
    begin->second -= found->second;
    mark_pair( *found );
  }
  else {
    add_unit_resolution( v, var_offset, begin->second );
    add_resolution( v, var_offset, *begin );
    add_resolution( v, var_offset, UnaryWeightedClause( found->first, begin->second ) );
    if ( found->second != begin->second ) {
      found->second -= begin->second;
    }
    else {
      mark_pair( *found );
    }
    mark_pair( *begin );
  }
}

void resolution_in_literal( const int v, const int var_offset ) {
  BinaryClauseList::iterator begin = clausesbc[ var_offset ].begin(),
    end = clausesbc[ var_offset ].end();
  //int distance = end - begin;
  while( begin != end ) { //--distance > 0 ) { //begin != end ) {
    BinaryClauseList::iterator found = find( begin + 1, end, 
					     make_offset( -unmake_offset( begin->first ) ) );
    if ( found != end ) {
      apply_literal_resolution( v, var_offset, begin, found );
    }
    do {
      begin++;
    } while( begin != end and pair_marked( *begin ) );
  }
  literal_cleaning( var_offset );
}

bool inverse_order( UnaryWeightedClause a, UnaryWeightedClause b ) {
  //return a.first > b.first; // Caution!! If >= the algorithm adds bad numbers
  return a.second > b.second; 
}

void resolution_rule_bc( const int var ) {
  for( int i = var+1; i < num_vars; i++ ) {
    resolution_in_literal( var, make_offset( i ) );
    resolution_in_literal( var, make_offset( -i ) );
    resolution_in_var( var, i );
  }
}
#endif // RESOLUTION_RULE

bool previous_not_satisfied( const Clause& clause ) {
  for( int i = 0; i < clause.length; i++ ) {
    if( i != clause.max_index && i != clause.penultimate_index ) {
      if ( make_literal( clause.literals[ i ] ) == 
	   partial_solution[ abs( clause.literals[ i ] ) ] ) {
	return false;
      }
    }
  }
  return true;
}

int drop( int var, int index_clause ) {
  int index = 0;
#ifdef DEBUG_ON
  cout << "Droping in var " << var << endl;
#endif
  while( clauses[ index_clause ].apn_value_abs == var 
	 && index_clause < num_long_clauses ) {
    if ( previous_not_satisfied( clauses[ index_clause ] ) ) {
      //cout << "Drop Index Clause " << index_clause << endl;
      add_clause_db( make_offset( clauses[ index_clause ].penultimate_value ),
		     make_offset( clauses[ index_clause ].max_value ), 
		     clauses[ index_clause ].weight );
      added_binary_clauses.push( make_offset( clauses[ index_clause ].penultimate_value ) );
      index++;
#ifdef MODE_TEST
      if( clauses[ index_clause ].weight == 0 ) {
	critical_error( "drop weight zero");
      }
#endif
    }
    index_clause++;
  }
  added_binary_clauses_index.push( index );

  return index_clause;
}

void back( int var, int index_clause ) {
  for( int i = 0; i < added_binary_clauses_index.top(); i++ ) {
#ifdef RANDOM_ACCESS
    clausesbc[ added_binary_clauses.top() ].pop_back();
#else
    clausesbc[ added_binary_clauses.top() ].pop_front();
#endif
    added_binary_clauses.pop();
  }
  added_binary_clauses_index.pop();
#ifdef DEBUG_ON
  cout << "Backing from var " << var << endl;
#endif
}

int star_rule_look_ahead( int var_in, int& length_star ) {
  int fc = 0, inc;
  for( int var = var_in, var2, min_weight; var <= num_vars; var++ ) {
    for( BinaryClauseList::iterator i = clausesbc[ make_offset( var ) ].begin(); 
	 i != clausesbc[ make_offset( var ) ].end(); i++ ) {
      var2 = unmake_offset( i->first );
      if( unit_clauses[ make_offset( -var ) ] > 0 && unit_clauses[ make_offset( -var2 ) ] > 0 ) {
	min_weight = min( i->second, min( unit_clauses[ make_offset( -var ) ], 
					  unit_clauses[ make_offset( -var2 ) ] ) );
        fc += min_weight;
	unit_stack.push( UnaryWeightedClause( make_offset( -var ), min_weight ) );
        unit_clauses[ make_offset( -var ) ] -= min_weight;
	length_star++;
	unit_stack.push( UnaryWeightedClause( make_offset( -var2 ), min_weight ) );
        unit_clauses[ make_offset( -var2 ) ] -= min_weight;
	length_star++;
      }
    }

    for( BinaryClauseList::iterator i = clausesbc[ make_offset( -var ) ].begin(); 
      i != clausesbc[ make_offset( -var ) ].end(); i++ ) {      
      var2 = unmake_offset( i->first );
      if( unit_clauses[ make_offset( var ) ] > 0 && unit_clauses[ make_offset( -var2 ) ] > 0 ) {
	min_weight = min( i->second, min ( unit_clauses[ make_offset( var ) ], 
					   unit_clauses[ make_offset( -var2 ) ] ) );
        fc += min_weight;
	unit_stack.push( UnaryWeightedClause( make_offset( var ), min_weight ) );
        unit_clauses[ make_offset( var ) ] -= min_weight;
	length_star++;
	unit_stack.push( UnaryWeightedClause( make_offset( -var2 ), min_weight ) );
        unit_clauses[ make_offset( -var2 ) ] -= min_weight;
	length_star++;	
      }
    }
  }
  return fc;
}

int up_look_ahead( int var_in, int& length_star ) {
  int fc = 0, inc;
  int *path = new int[ num_vars+1 ];
  fill( &path[0], &path[num_vars], 0 );
  
  for( int var = var_in+1; var <= num_vars; var++ ) {
    inc = min( unit_clauses[ make_offset( var ) ], unit_clauses[ make_offset( -var ) ] );    
    if ( inc > 0 ) {
      fc += inc;
      unit_clauses[ make_offset( var ) ] -= inc;
      unit_stack.push( UnaryWeightedClause( make_offset( var ), inc ) );
      length_star++;	
      unit_clauses[ make_offset( -var ) ] -= inc;
      unit_stack.push( UnaryWeightedClause( make_offset( -var ), inc ) );      
      length_star++;	
      break;
    }    
    if( unit_clauses[ make_offset( var ) ] > 0 ) {
      for( BinaryClauseList::iterator i = clausesbc[ make_offset( -var ) ].begin(); i != clausesbc[ make_offset( -var ) ].end(); i++ ) {
	if ( path[ i->first/2 ] == 0 ) {
	path[ i->first/2 ] = var;
	  inc = min( i->second, unit_clauses[ make_offset( var ) ] );
	  unit_clauses[ i->first ] += inc;
	  unit_stack.push( UnaryWeightedClause( i->first, -inc ) );
	  length_star++;
	}
      }      
    }
    if ( unit_clauses[ make_offset( -var ) ] > 0 ) {
      for( BinaryClauseList::iterator i = clausesbc[ make_offset( var ) ].begin(); i != clausesbc[ make_offset( var ) ].end(); i++ ) {
	if ( path[ i->first/2 ] == 0 ) {
	  path[ i->first/2 ] = -var;
	  inc = min( i->second, unit_clauses[ make_offset( -var ) ] );
	  unit_clauses[ i->first ] += inc;
	  unit_stack.push( UnaryWeightedClause( i->first, -inc ) );	  
	  length_star++;
	}
      }      
    }         
  }
  delete path;
  //if ( fc > 0 ) cout << "FC: " << fc << endl;
  return fc;
}

#ifdef STAR_RULE_IR
void star_rule_ir( int var, int& unsat, int& length_star, int& length_binary ) {
  int literal_null, var_null =  unit_clauses[ make_offset( var ) ] > 0 ? -var : var;
  for( BinaryClauseList::iterator i = clausesbc[ make_offset( var_null ) ].begin(); 
       unit_clauses[ make_offset( -var_null ) ] > 0 and unit_clauses[ make_complementary( i->first ) ] > 0 and
	 i != clausesbc[ make_offset( var_null ) ].end(); 
       i++ ) {
    min_weight = min ( min( unit_clauses[ make_offset( -var_null ) ], unit_clauses[ make_complementary( i->first ) ] ), i->second );
    if ( min_weight > 0 ) {
      unsat += min_weight;
      binary_stack_min_weight.push( min_weight );
      literal_null = make_complementary( i->first );
      unit_clauses[ make_offset( -var_null ) ] -= min_weight;
      unit_stack.push( UnaryWeightedClause( make_offset( -var_null ), min_weight ) );
      unit_clauses[ literal_null  ] -= min_weight;
      unit_stack.push( UnaryWeightedClause( literal_null, min_weight ) );
      i->second -= min_weight;
      binary_stack_unit_pointer.push( &(i->second) );
      add_clause_db( make_offset( -var_null ), literal_null, min_weight );
      binary_stack_new.push( make_offset( -var_null ) );
      length_binary++;
    }
  }
}
#endif

int forward_checking( int var_in, int index_clause, 
		      int& length_cuc, int& length_star, int& unsat, int& length_binary ) {
  int fc = 0, inc;
  length_cuc = length_star = 0;
  length_binary = 0;

  for( int var = var_in; var <= num_vars; var++ ) {
    inc = min( unit_clauses[ make_offset( var )  ], unit_clauses[ make_offset( -var ) ] );
#ifdef CUC_RULE
    unsat += inc;
#else
    fc += inc;
#endif
    if( inc > 0 ) {
      unit_clauses[ make_offset( var ) ] -= inc;
      unit_stack.push( UnaryWeightedClause( make_offset( var ), inc ) );
      length_cuc++;
      unit_clauses[ make_offset( -var ) ] -= inc;
      unit_stack.push( UnaryWeightedClause( make_offset( -var ), inc ) );
      length_cuc++;
    }
  }

#ifdef STAR_RULE_IR
  star_rule_ir( var_in, unsat, length_star, length_binary );
#endif  
#ifdef LB4
  for( int var = var_in, var_null, literal_null; var <= num_vars; var++ ) {
    if( unit_clauses[ make_offset( var ) ] + unit_clauses[ make_offset( -var ) ] > 0 ) {
      inc = min( unit_clauses[ make_offset( var )  ], unit_clauses[ make_offset( -var ) ] );
      if( inc > 0 ) {
	fc += inc;
	unit_clauses[ make_offset( var ) ] -= inc;
	unit_stack.push( UnaryWeightedClause( make_offset( var ), inc ) );
	length_star++;
	unit_clauses[ make_offset( -var ) ] -= inc;
	unit_stack.push( UnaryWeightedClause( make_offset( -var ), inc ) );
	length_star++;
      }
      var_null =  unit_clauses[ make_offset( var ) ] > 0 ? -var : var;
      for( BinaryClauseList::iterator i = clausesbc[ make_offset( var_null ) ].begin(); 
	   unit_clauses[ make_offset( -var_null ) ] > 0 and i != clausesbc[ make_offset( var_null ) ].end(); 
	   i++ ) {
	min_weight = min( unit_clauses[ make_offset( -var_null ) ], i->second );
	if ( min_weight > 0 ) {
	  literal_null = i->first;
	  unit_clauses[ make_offset( -var_null ) ] -= min_weight;
	  unit_stack.push( UnaryWeightedClause( make_offset( -var_null ), min_weight ) );
	  length_star++;	
	  unit_clauses[ literal_null  ] += min_weight;
	  unit_stack.push( UnaryWeightedClause( literal_null, -min_weight ) );
	  length_star++;
	}//if
      }//for
    }//if
  }//for
#endif

#ifdef UP_LOOK_AHEAD
  fc += up_look_ahead( var_in, length_star );
#endif
#ifdef STAR_RULE
  fc += star_rule_look_ahead( var_in, length_star );
#endif
  //if ( fc > 0 ) cout << "FC: " << fc << endl;
  
#ifdef MODE_TEST
  if ( fc < 0 ) critical_error( "Negative FC" );
#endif
#ifdef DEBUG_ON
  cout << "FC: " << fc << " unsat: " << unsat << endl;
#endif
  
  return fc;
}

void undo_forward_checking( int length ) {
  for( int i = 0; i < length; i++ ) {
    unit_clauses[ unit_stack.top().first ] += unit_stack.top().second;
    unit_stack.pop();
  }
}

#ifdef STAR_RULE_IR
void undo_inference( int length ) {
  int inc;
  undo_forward_checking( length*2 );
  BinaryClauseList::iterator iter;
  for( int i = 0; i < length; i++ ) {
    inc = binary_stack_min_weight.top();
    *(binary_stack_unit_pointer.top()) += inc;
    binary_stack_unit_pointer.pop();
    binary_stack_min_weight.pop();
    clausesbc[ binary_stack_new.top() ].pop_back();
    binary_stack_new.pop();
  }
}
#endif

int compute_total_weight( int literal ) {
  int total = 0;
  for( BinaryClauseList::iterator i = clausesbc[ literal ].begin(); 
       i != clausesbc[ literal ].end(); i++ ) {
    total += i->second;
  }
  return total;
}

//
// Brach and Bound 
//

void solve_MaxSAT( int var, int index_clause, int unsat ) {
  int fc, gap;
#ifdef DUC_RULE
  int length[] = {0, 0};
#endif
  //int unit[ MAX_VARS* 2 ], weights[ MAX_VARS * 2 ];
  int length_cuc, length_star, length_binary;

#ifdef DEBUG_ON
  cout << "DEBUG: Starting var " << var << " clause " << index_clause 
       << " and unsat " << unsat  << endl;
  int count = 0;
  for( int i = 1; i <= num_vars; i++ ) {
    count += unit_clauses[ 2*i+ TRUE ] + unit_clauses[ 2*i+FALSE ];
  }
  cout << "Number of unit clauses: " << count << endl;
  print_list( cout, &unit_clauses[2], &unit_clauses[(2*num_vars)+2], ' ' ); cout << endl;
#endif
#ifdef MODE_TEST
  //assert( index_clause < num_clauses );
  if ( index_clause > num_clauses ) {
    critical_error( "Too many clauses" );
  }
  if ( var > last_var+1 ) {
    critical_error( "Too many variables" );
  }
#endif
  var++;
  int new_index_clause;
  if( index_clause < num_long_clauses ) {
    new_index_clause = drop( var-1, index_clause );
  }
  else {
    new_index_clause = num_long_clauses;
  }

  //if ( var > last_var ) {
  if ( new_index_clause == num_long_clauses && var == num_vars ) {
#ifdef DEBUG_ON
    cout << "var " << var << " last " << last_var << endl;
#endif
    unsat += forward_checking( var, num_long_clauses, length_cuc, length_star, unsat, length_binary );
    undo_forward_checking( length_cuc+length_star ); //unit, weights, length_unit );
#ifdef STAR_RULE_IR
    undo_inference( length_binary );
#endif
    if ( unsat < ub ) {
#ifdef MODE_TEST
      if ( stop_point > unsat ) {
#ifdef DEBUG_ON
        cout << "unsat: " << unsat << endl;
	cout << print_list( cout, &partial_solution[1], &partial_solution[ num_vars+1 ], ' ' ); cout << endl;
#endif
        cout << "Stop point: " << stop_point << endl;
        critical_error( "Stop point reached" );
      }
#endif
#ifdef DEBUG_ON
      cout << "Leaf: " << unsat << endl;
#endif
      if ( unit_clauses[ 2*num_vars+TRUE ] < unit_clauses[ 2*num_vars+FALSE ] )
        partial_solution[ num_vars ] = FALSE;
      else
        partial_solution[ num_vars ] = TRUE;
      
      ub = unsat;
      cout << "o " << ub << endl;
      for( int i = 1; i <= num_vars; i++ )
	solution[ i ] = partial_solution[ i ];
    }
    backtracks++;
#ifdef UNIT_PROPAGATION
    unit_value[ var-1 ] = UNDEF;
#endif
    if( index_clause < num_long_clauses ) {
      back( var-1, index_clause );
    }
    return;
  }

#ifdef LOOK_AHEAD
  fc = forward_checking( var, new_index_clause, length_cuc, length_star, unsat, length_binary );
#else
  fc = 0;
#endif

  if( unsat + fc >= ub ) {
#ifdef DEBUG_ON
    cout << "Backtrack FC" << endl;
#endif
    backtracks++; 
#ifdef UNIT_PROPAGATION
    undo_unit_propagation( var ); 
#endif
#ifdef LOOK_AHEAD
    undo_forward_checking( length_cuc+length_star ); //unit, weights, length_unit );
#ifdef STAR_RULE_IR
    undo_inference( length_binary );
#endif
#endif
    if( index_clause < num_long_clauses ) {
      back( var-1, index_clause );
    }
    return; 
  }

#ifdef UNIT_PROPAGATION
  if( ub - unsat <= min_weight ) {
    if ( unit_propagation( var ) ) {
      undo_unit_propagation( var );
#ifdef LOOK_AHEAD
      undo_forward_checking( length_cuc+length_star ); //unit, weights, length_unit );
#ifdef STAR_RULE_IR
      undo_inference( length_binary );
#endif
#endif
      backtracks++;
      if( index_clause < num_long_clauses ) {
	back( var-1, index_clause );
      }
      return;
    }
  }
#endif

#ifdef DUC_RULE
  check_clauses_bc( var, index_clause, length );
#endif

#ifdef LOOK_AHEAD
  gap = unit_clauses[ TRUE + 2*var ] - unit_clauses[ FALSE + 2*var ];
#ifdef CUC_RULE
  undo_forward_checking( length_star );
#else
  undo_forward_checking( length_cuc+length_star ); //unit, weights, length_unit );
#endif
#else
  gap = 0;
#endif

  if ( 
#ifdef UNIT_PROPAGATION
      (unit_value[ var ] == UNDEF || unit_value[ var ] == TRUE) &&
#endif
      unsat + fc - gap < ub
#ifdef DUC_RULE
      && unit_clauses[ FALSE + 2*var ] <= 
      compute_total_weight( TRUE + 2*var ) + unit_clauses[ TRUE + 2*var ]
#endif 
      ) 
    {
      partial_solution[ var ] = TRUE;
      add_unit_clauses_bc( make_offset( -var ) );
      solve_MaxSAT( var, new_index_clause, unsat + unit_clauses[ FALSE + 2*var ] );
      remove_unit_clauses_bc( make_offset( -var ) );
    }
  else {
    backtracks++;
#ifdef DEBUG_ON
    cout << "Skip FC - TRUE" << endl;
#endif
  }

  if (
#ifdef UNIT_PROPAGATION
      (unit_value[ var ] == UNDEF || unit_value[ var ] == FALSE) &&
#endif
      unsat + fc + gap < ub
#ifdef DUC_RULE
      && unit_clauses[ TRUE + 2*var ] <= 
      compute_total_weight( FALSE + 2*var ) + unit_clauses[ FALSE + 2*var ]
#endif
      ) 
    {
      partial_solution[ var ] = FALSE;
      add_unit_clauses_bc( make_offset( var ) );
      solve_MaxSAT( var, new_index_clause, unsat + unit_clauses[ TRUE + 2*var ] );  
      remove_unit_clauses_bc( make_offset( var ) );
    }
  else {
    backtracks++;
#ifdef DEBUG_ON
    cout << "Skip FC - FALSE" << endl;
#endif
  }

#ifdef CUC_RULE
  undo_forward_checking( length_cuc );
#endif
#ifdef STAR_RULE_IR
  undo_inference( length_binary );
#endif

  if( index_clause < num_long_clauses ) {
    back( var-1, index_clause );
  }
#ifdef UNIT_PROPAGATION
  undo_unit_propagation( var );
#endif
}

void return_unknown() {
  cout << "s UNKNOWN" << endl;
  exit( 1 );
}

//
// Main
//

int main( int argc, char *argv[] ) {
#ifdef LOCAL_SEARCH
  ub = local_search( argv[1] ) + 1;
  cout << "c Total weight " << total_weight << endl;
  if ( ub < 0 ) ub = total_weight;
  if ( ub < 0 ) return_unknown();
  readfile( argv[1] );
#else
  readfile( argv[1] );

#ifdef MANUAL_ORDERING
  int t, n = 2, my_order[MAX_VARS];
  do {
    t = atoi(argv[n++]);
    my_order[n - 2] = t;
  } while(t);
#endif

#ifdef MODE_TEST
  if ( argc < 3 ) critical_error( "Error: Mode test needs two parameters" );
  ub = total_weight;//num_clauses * max_weight;
  stop_point = atoi( argv[2] );
#else
#ifdef MANUAL_ORDERING
  ub = argc < 3 ? total_weight : atoi( argv[ n ] );
#else
  ub = argc < 3 ? total_weight : atoi( argv[ 2 ] );
#endif
#endif
#endif

  if ( num_vars >= MAX_VARS or num_clauses >= MAX_CLAUSES )
    return_unknown();

  cout << "c Initial ub=" << ub << endl;
  backtracks = 0;
  cout << "c Max weight " << max_weight << endl;
  cout << "c Min weight " << min_weight << endl;
#ifdef RESOLUTION_RULE
  resolution_list = new ResolutionList[ num_vars+1 ];
  unit_resolution_list = new UnaryList[ num_vars+1 ];
#endif

  //if ( ub ) {
    int mapping[ MAX_VARS ];

#ifdef NEIGHBOURS
    neighbours_ordering();
#endif

    sort( var_map + 1, var_map + num_vars + 1, variable_ordering );

#ifdef DEBUG_ON
    printf("Current order: ");
    for(int i = 1; i <= num_vars; i++) printf(" %d", var_map[i]);
    printf("\n");
#endif

#ifdef MANUAL_ORDERING
    for(int i = 1; i <= num_vars; i++)
      var_map[i] = my_order[i];
#ifdef DEBUG_ON
    printf("Manual order: ");
    for(int i = 1; i <= num_vars; i++) printf(" %d", var_map[i]);
    printf("\n");
#endif
#endif

    var_mapping( mapping );

    update_clause_max_value();  
    
    sort( clauses, clauses + num_clauses );

#ifdef DEBUG_ON    
    //    cout << "Starting clauses" << endl;
    //cout << print_list( cout, clauses, clauses + num_clauses, '\n' );
#endif    

    create_binary_clause_db();

#ifdef DEBUG_ON    
    //cout << "Clauses" << endl;
    //cout << print_list( cout, clausesbc, clausesbc + (2*num_vars+2), '\n' );
    //cout << "Long clauses" << endl;
    //cout << print_list( cout, clauses, clauses + num_long_clauses, '\n' );
#endif    
#ifdef MODE_TEST
    check_runtime_error();
#endif    
#ifdef RESOLUTION_RULE
    resolution_rule_bc( 0 );
#endif

    //cout << "Binary clauses" << endl;
    //cout << print_list( cout, clausesbc, clausesbc + (2*num_vars+2), '\n' );    
    solve_MaxSAT( 0, 0, 0 );
    //cout << "Binary clauses" << endl;
    //cout << print_list( cout, clausesbc, clausesbc + (2*num_vars+2), '\n' );

#ifdef DEBUG_ON    
    //cout << "Clauses" << endl;
    //cout << print_list( cout, &clausesbc[ make_offset( -1 ) ], 
    //			&clausesbc[ make_offset( num_vars ) + 1 ], '\n' );
#ifdef RESOLUTION_RULE
    cout << "Resolution" << endl;
    for( int i = 1; i <= num_vars; i++ ) {
      cout << "res[" << i << "] ";
      copy( resolution_list[ i ].begin(), resolution_list[ i ].end(), 
	    ostream_iterator<ResolutionInfo>( cout, " " ) );
    }    
    cout << endl;
#endif
#endif   

#ifdef MODE_TEST
    if ( ub != atoi( argv[ 2 ] ) ) {
      cerr << "Error: do not match" << endl;
      cout << "Error: expected ub " << atoi( argv[ 2 ] ) << " and found ub " << ub;
      cout << " do not match" << endl;
    }
#endif
    //}
  
  cout << "c Best solution: " << ub << " unsat" << endl;
  cout << "c Backtracks: " << backtracks << endl;
  cout << "o " << ub << endl;
  cout << "s OPTIMUM FOUND" << endl;
  cout << "v ";
  for( int i = 1; i <= num_vars; i++ ) {
    if( solution[ mapping[i] ] != TRUE ) cout << "-";
    cout << i << " ";
  }
  cout << endl;

#ifdef DEBUG_ON
  cout << "Solution" << endl;
  copy( &solution[ 1 ], &solution[ num_vars + 1], ostream_iterator<int>( cout, " " ) );
  cout << endl;
  cout << "Unmapped solution" << endl;
  for( int i = 1; i <= num_vars; i++ ) {
    cout << solution[ var_map[ i ] ] << " ";
  }
  cout << endl;
#endif

  return 0;
}
