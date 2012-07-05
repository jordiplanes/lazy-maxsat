/*
 * Code been developed in Universitat de Lleida / CCIA
 * 
 * Created to solve MaxSAT CNF instances.
 * Usage: maxsat <file.cnf> <upper-bound>
 *
 * Creation date: June 2nd, 2004
 *
 * To do: recursive -> iterative
 *
 */

// Alerts //!!

#include <cstdio>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <iterator>
#include <list>
#include <vector>
//#include <ext/slist>

//#include "simplelist.h"
#include "stack.h"

using namespace std;
using namespace __gnu_cxx;

extern "C" {
  int local_search( char* );
}

/*
 * GLOBAL FLAGS
 */

//#define DEBUG_ON
//#define MODE_TEST

#define RANDOM_ACCESS
typedef vector<int> BinaryClauseList;
//#include "simplelist.h"
//typedef SimpleList<int,50> BinaryClauseList;

/*
 * ALGORITHM FLAGS
 */

//#define LOCAL_SEARCH
#define UNIT_PROPAGATION
#define UNIT_CLAUSE_ELIMINATION
#define VAR_MAPPING
#define LOOK_AHEAD
#define NEIGHBOURS
#define BACKBONE
#define DUC_RULE
//#define ONLY_2SAT
#define STAR_RULE
#define RESOLUTION_RULE
//#define MANUAL_ORDERING

/*
 * CONSTANTS
 */

#define MAX_LINE 255
#define MAX_VARS 1600
#define MAX_CLAUSES 100000
#define MAX_LENGTH 27
#define MAX_UNIT 350
#define FALSE 0
#define TRUE 1
#define UNDEF -1

struct Clause {
  int literals[MAX_LENGTH];
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
stack<int,MAX_CLAUSES> future_unit;
#ifdef MODE_TEST
int stop_point;
#endif

#ifdef RESOLUTION_RULE
typedef pair<int,int> ResolutionInfo;
list<ResolutionInfo> *resolution_list;
typedef list<int> UnitList;
UnitList *unit_resolution_list;
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

// Operators

Clause& Clause::operator=( const Clause& s ) {
  length = s.length;
  for( int i = 0; i < length; i++ ) {
    literals[ i ] = s.literals[ i ];
  }
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
  return variables[ begin ].count >= variables[ end ].count;
#else
  return variables[ end ].count == 0;
#endif
}

// Printings
#ifdef DEBUG_ON
template <class Iterator>
void print_list( const Iterator begin, const Iterator end, char separator ) {
  for( Iterator iter = begin; iter != end; iter++ ) {
    cout << "[" << iter - begin << "]" << *iter << separator;
  }
}

ostream& operator<<( ostream& os, const Clause& c ) {
  copy( c.literals, c.literals + c.length, ostream_iterator<int>(os, " ") );
  os << "(" << c.max_value << "," << c.max_index << ")";
  os << "(" << c.penultimate_value << "," << c.penultimate_index << ")";
  os << "(" << c.apn_value << "," << c.apn_index << ")";
  return os;
}

ostream& operator<<( ostream& os, BinaryClauseList bcl) {
  copy( bcl.begin(), bcl.end(), ostream_iterator<int>( os, " " ) );
  return os;
}

ostream& operator<<( ostream& os, const Variable& v ) {
  os << "(" << "c=" << v.count << " w=" << v.weight << ")";
  return os;
}

void print_status() {
  cout << "Status" << endl;
  cout << "Binary clauses" << endl;
  for( int i = 1; i <= (2*num_vars)+1; i++ ) {
    cout << "(" << unmake_offset( i ) << ") ";
    print_list( clausesbc[ i ].begin(), clausesbc[ i ].end(), ' ' );
  }
  cout << endl;
  cout << "Unit clauses" << endl;
  print_list( &unit_clauses[ 1 ], &unit_clauses[ (2*num_vars)+2 ], ' ');
  cout << endl;
}
#endif
// Debuging

void critical_error( char* message ) {
#ifdef DEBUG_ON
  cout << "Clauses" << endl;
  print_list( clausesbc, clausesbc + (2*num_vars+2), '\n' );
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

  do {
    ifs.getline( line, MAX_LINE );
  } while ( line[0] == 'c' );

  sscanf( line, "p cnf %d %d", &num_vars, &num_clauses );
  
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
    int max_length = 1, num_uc = 0;
#endif

  for( int i = 0, j, k; i < num_clauses; i++ ) {
    ifs >> k;
    for(j = 0; k != 0; j++) {
      variables[ abs(k) ].count++;
      variables[ abs(k) ].literal_count[ make_literal(k) ]++;      
      clauses[i].literals[j] = k;
      ifs >> k;
    }    
    clauses[i].length = j;
#ifdef MODE_TEST
    max_length = max( max_length, j );
#endif
   
#ifdef UNIT_CLAUSE_ELIMINATION
    if ( clauses[i].length == 1 ) {
      int& literal = clauses[i].literals[0];
#ifdef DEBUG_ON
      cout << "Unit clause " << literal << " removed" << endl;
#endif
#ifdef MODE_TEST
      num_uc++;
#endif
      unit_clauses_pre[ 2 * abs( literal ) + make_literal( literal ) ]++;
      variables[ abs( literal ) ].count--;
      variables[ abs(k) ].literal_count[ make_literal(k) ]--;
      i--;
      num_clauses--;
    }
#endif
  }

#ifdef MODE_TEST
  if ( !ifs.good() ) {
    critical_error( "Error reading the file" );
  }
  cout << "Unit clauses removed: " << num_uc << endl;
  if ( num_uc >= MAX_UNIT ) {
    critical_error( "MAX_UNIT exceeded" );
  }
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

inline void add_clause_db( int penultimate, int last ) {
#ifdef RANDOM_ACCESS
    clausesbc[ penultimate ].push_back( last );
#else
    clausesbc[ penultimate ].push_front( last );
#endif
}

inline void remove_clause_db( int penultimate, int last ) {
#ifdef MODE_TEST
  if ( clausesbc[ penultimate ].empty() ) { critical_error( "Empty clausesbc" ); }
#endif
  BinaryClauseList::iterator i = find( clausesbc[ penultimate ].begin(), clausesbc[ penultimate ].end(), last );
#ifdef MODE_TEST
  if( i == clausesbc[ penultimate ].end() ) { critical_error( "Clause not found" ); }
#endif
  clausesbc[ penultimate ].erase( i );

  /*
#ifdef RANDOM_ACCESS
  clausesbc[ penultimate ].pop_back();
#else
  clausesbc[ penultimate ].pop_front();
#endif
  */
}

bool null_clause( Clause c ) {
  return c.penultimate_value == 0;
}

void set_null_clause( Clause& c ) {
  c.penultimate_value = 0;
}

void create_binary_clause_db() {
  for( int c = 0; c < num_clauses; c++ ) {
    if ( clauses[c].length == 2 ) {
#ifdef DEBUG_ON
      cout << "Adding " << make_offset( clauses[c].penultimate_value ) << " " << 
	make_offset( clauses[c].max_value ) << endl;
#endif
      add_clause_db( make_offset( clauses[ c ].penultimate_value ),
		     make_offset( clauses[ c ].max_value ) );
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

void find_future_literals( int var, int index, int future[ 2 ] ) {
  future[ 0 ] = future[ 1 ] = 0;
  for( ; index < num_clauses; index++ ) {
    if ( clauses[ index ].length > 2 )
      for( int i = 0; i < clauses[ index ].length; i++ )       
	if ( abs( clauses[ index ].literals[ i ] ) == var ) {
	  future[ make_literal( clauses[ index ].literals[ i ] ) ]++;
	  break;
	}
  }
#ifdef DEBUG_ON
  cout << "DEBUG: " << future[ TRUE ] << ", " << future[ FALSE ] << endl;
#endif
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

void check_clauses_bc( int var, int index_clause, int length[ 2 ] ) {
#ifdef DUC_RULE
  /* Counting 2-SAT */
  length[ TRUE ] = clausesbc[ make_offset( var ) ].size();
  length[ FALSE] = clausesbc[ make_offset( -var )].size();
  /*
  for( int v = var+1; v <= num_vars; v++ ) {
    length[ TRUE ] += count( clausesbc[ make_offset( v ) ].begin(), 
			     clausesbc[ make_offset( v ) ].end(), make_offset( var ) );
    length[ TRUE ] += count( clausesbc[ make_offset( -v ) ].begin(), 
			     clausesbc[ make_offset( -v ) ].end(), make_offset( var ) );
    length[ FALSE ] += count( clausesbc[ make_offset( v ) ].begin(), 
			      clausesbc[ make_offset( v ) ].end(), make_offset( -var ) );
    length[ FALSE ] += count( clausesbc[ make_offset( -v ) ].begin(), 
			      clausesbc[ make_offset( -v ) ].end(), make_offset( -var ) );
  }
  */
  /* Counting 3-SAT */ //
#ifndef ONLY_2SAT
  while( clauses[ index_clause ].apn_value_abs < var && index_clause < num_clauses ) {    
    if( clauses[ index_clause ].max_value_abs == var ) {
      length[ clauses[ index_clause ].max_literal ]++;
    } 
    else if ( clauses[ index_clause ].penultimate_value_abs == var &&
	      clauses[ index_clause ].max_literal !=
	      partial_solution[ clauses[ index_clause ].max_value_abs ] ) {
      length[ clauses[ index_clause ].penultimate_literal ]++;
    }
    index_clause++;
  }
  for( ; clauses[ index_clause ].apn_value_abs == var; index_clause++ ) {
    length[ clauses[ index_clause ].apn_literal ]++;
  }
#endif  
#endif
}

void add_unit_clauses_bc( int literal ) {
  for( BinaryClauseList::iterator i = clausesbc[ literal ].begin(); i != clausesbc[ literal ].end(); i++ ) {
    unit_clauses[ *i ]++;
  }
}

void remove_unit_clauses_bc( int literal ) {
  for( BinaryClauseList::iterator i = clausesbc[ literal ].begin(); i != clausesbc[ literal ].end(); i++ ) {
    unit_clauses[ *i ]--;
  }
}

bool unit_propagation( int var ) {
  while( var <= num_vars ) {
    if ( unit_clauses[ FALSE + 2*var ] > 0 && unit_clauses[ TRUE + 2*var ] > 0 ) {
      return true;
    }
    if ( unit_clauses[ FALSE + 2*var  ] > 0 ) {
      unit_value[ var++ ] = FALSE;
    }
    else if ( unit_clauses[ TRUE + 2*var ] > 0 ) {
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

inline void literal_cleaning( const int var ) {
  clausesbc[var].erase( remove( clausesbc[var].begin(), clausesbc[var].end(), 0 ), 
			clausesbc[var].end() );
}

inline void add_resolution( int var, int var1, int var2 ) {
  resolution_list[ var ].push_back( ResolutionInfo( var1, var2 ) );
}

inline void add_unit_resolution( int var, int unit ) {
  unit_clauses[ unit ]++;
  unit_resolution_list[ var ].push_back( unit );
}

void remove_resolutions( int var ) {
  list<ResolutionInfo>::iterator i = resolution_list[ var ].begin(),
    end = resolution_list[ var ].end();
  for( ; i != end; i++ ) {
    add_clause_db( i->first, i->second );
  }
  resolution_list[ var ].clear();
  UnitList::iterator j = unit_resolution_list[ var ].begin(),
    end2 = unit_resolution_list[ var ].end();
  for( ; j != end2; j++ ) {
    unit_clauses[ *j ]--;
  }
  unit_resolution_list[ var ].clear();
}

void resolution_in_literal( const int v, const int var_offset ) {
  BinaryClauseList::iterator begin = clausesbc[ var_offset ].begin(),
    end = clausesbc[ var_offset ].end();
  int distance = end - begin;
  while( --distance > 0 ) { //begin != end ) {
    BinaryClauseList::iterator found = find( begin + 1, end, -(*begin) );
    if ( found != end ) {
      add_unit_resolution( v, var_offset );
      add_resolution( v, var_offset, *begin );
      add_resolution( v, var_offset, *found );
      *begin = 0;
      *found = 0;
    }
    begin++;
  }
  literal_cleaning( var_offset );
}

void resolution_in_var( const int v, const int var ) { 
  BinaryClauseList::iterator begin_p = clausesbc[ make_offset( var ) ]. begin(),
    end_p = clausesbc[ make_offset( var ) ].end();
  while( begin_p != end_p ) {
    BinaryClauseList::iterator begin_n = clausesbc[ make_offset( -var ) ]. begin(),
      end_n = clausesbc[ make_offset( -var ) ].end();
    BinaryClauseList::iterator found = find( begin_n, end_n, *begin_p );
    if ( found != end_n ) {
      add_unit_resolution( v, *begin_p );
      add_resolution( v, make_offset( var ), *begin_p );
      add_resolution( v, make_offset( -var ), *found );
      *begin_p = 0;
      *found = 0;
    }
    begin_p++; 
  }
  literal_cleaning( make_offset( var ) );
  literal_cleaning( make_offset( -var ) );
}

bool inverse_order( int a, int b ) {
  return a > b; // Caution!! If >= the algorithm adds bad numbers
}

void resolution_rule_bc( const int var ) {
  for( int i = 1; i <= num_vars; i++ ) {
    
#ifdef RANDOM_ACCESS    
    sort( clausesbc[ make_offset( i ) ].begin(), 
	  clausesbc[ make_offset( i ) ].end(), inverse_order );
    sort( clausesbc[ make_offset( -i ) ].begin(),
	  clausesbc[ make_offset( -i ) ].end(), inverse_order );
#endif
    
    //resolution_in_literal( var, make_offset( i ) );
    //resolution_in_literal( var, make_offset( -i ) );
    resolution_in_var( var, i );
  }
}
#endif // RESOLUTION_RULE

/*
void clauses_cleaning() {
  int source = 0, index_clause;
  for( index_clause = 0; index_clause < num_clauses; index_clause++, source++ ) {
    while( clauses[ source ].max_value == 0 && source < num_clauses ) source++; 
    clauses[ index_clause ] = clauses[ source ];
  }
  set_null_clause( clauses[ index_clause ] );
}

void resolution_rule() {
  int index_clause;
  int pairs[ 2*MAX_VARS ][ 2*MAX_VARS ];

  for( int i = 1; i <= num_vars; i++ ) {
    for( int j = 1; j <= num_vars; j++ ) {
      pairs[ 2*i + TRUE ][ 2*j + TRUE] = -1;
      pairs[ 2*i + TRUE ][ 2*j + FALSE] = -1;
      pairs[ 2*i + FALSE ][ 2*j + TRUE] = -1;
      pairs[ 2*i + FALSE ][ 2*j + FALSE] = -1;
    }
  }
  for( index_clause = 0; index_clause < num_clauses; index_clause++ ) {
    int& var1 = clauses[index_clause].penultimate_value_abs; 
    int& sense1 = clauses[index_clause].penultimate_literal;
    int& var2 = clauses[index_clause].max_value_abs_2;
    int& sense2 = clauses[index_clause].max_literal;
    pairs[ 2*var1 + sense1 ][ var2 + sense2 ] = index_clause;
    //pairs[ var2 + sense2 ][ 2*var1 + sense1 ]++;
  }
  int resolution_counter = 0;
  for( int i = 1; i <= num_vars; i++ ) {
    for( int j = 1; j <= num_vars; j++ ) {
      if( pairs[ 2*i + TRUE ][ 2*j + TRUE ] >= 0 && pairs[ 2*i + TRUE ][ 2*j + FALSE ] >= 0 ) {
	clauses[ pairs[ 2*i + TRUE ][ 2*j + TRUE ] ].max_value = 0;
	clauses[  pairs[ 2*i + TRUE ][ 2*j + FALSE ] ].max_value = 0;
	num_clauses = num_clauses - 2;
	unit_clauses[ 2*i + TRUE ]++;
	//unit[ length++ ] = -(TRUE + 2*i);
	resolution_counter++;
      }
      if( pairs[ 2*i + FALSE ][ 2*j + TRUE ] >= 0 && pairs[ 2*i + FALSE ][ 2*j + FALSE ] >= 0 ) {
	clauses[ pairs[ 2*i + FALSE ][ 2*j + TRUE ] ].max_value = 0;
	clauses[ pairs[ 2*i + FALSE ][ 2*j + FALSE ] ].max_value = 0;
	num_clauses = num_clauses - 2;
	unit_clauses[ 2*i + FALSE ]++;
	//unit[ length++ ] = -(FALSE + 2*i);
	resolution_counter++;
      }
    }
  }
  clauses_cleaning();

  cout << "Resolution applied " << resolution_counter << " times" << endl;
#ifdef DEBUG_ON
  cout << "New num of clauses " << num_clauses << endl;
#endif
}
*/
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
#ifdef DEBUG_ON
  cout << "Dropping with var " << var << endl;
  //print_list( clausesbc, clausesbc + (2*num_vars+2), '\n' );    
#endif
  while( clauses[ index_clause ].apn_value_abs == var 
	 && index_clause < num_long_clauses ) {
    if ( previous_not_satisfied( clauses[ index_clause ] ) ) {
#ifdef DEBUG_ON
      cout << "Adding binary " << clauses[index_clause].penultimate_value << ", " 
	   << clauses[index_clause].max_value << endl;
#endif
      add_clause_db( make_offset( clauses[ index_clause ].penultimate_value ),
		     make_offset( clauses[ index_clause ].max_value ) );
    }
    index_clause++;
  }
#ifdef RESOLUTION_RULE
  //resolution_rule_bc( var );
#endif
  return index_clause;
}

void back( int var, int index_clause ) {
#ifdef RESOLUTION_RULE
  //remove_resolutions( var );
#endif
  while( clauses[ index_clause ].apn_value_abs == var 
	 && index_clause < num_long_clauses ) {
    if ( previous_not_satisfied( clauses[ index_clause ] ) ) {
      remove_clause_db( make_offset( clauses[ index_clause ].penultimate_value ),
			make_offset( clauses[ index_clause ].max_value ) );
    }
    index_clause++;
  }
#ifdef DEBUG_ON
  cout << "Backing from var " << var << endl;
#endif
}

int forward_checking( int var_in, int index_clause, int& length1, int& length2, int& unsat ) {
  int fc = 0, inc;

#ifdef DEBUG_ON
  print_status();
#endif
  length1 = length2 = 0;
  for( int var = var_in; var <= num_vars; var++ ) {
    inc = min( unit_clauses[ TRUE + 2*var ], unit_clauses[ FALSE + 2*var ] );
    //fc += inc;
    unsat += inc;
#ifdef DEBUG_ON
    if ( inc > 0 ) {
      cout << "FC(1) applied on var " << var << ": " << inc << " times" << endl;
    }
#endif
    for( int i = 0; i < inc; i++ ) {
      unit_clauses[ TRUE + 2*var ]--; 
      //unit[ length++ ] = (TRUE + 2*var);
      future_unit.push( TRUE + 2*var );
      length1++;
      unit_clauses[ FALSE + 2*var ]--;
      //unit[ length++ ] = (FALSE +2*var);
      future_unit.push( FALSE + 2*var );
      length1++;
    }    
  }
#ifdef DEBUG_ON
  cout << "FC(1): " << fc << endl;
#endif
  
#ifdef STAR_RULE
  for( int var = var_in, var2; var <= num_vars; var++ ) {
    for( BinaryClauseList::iterator i = clausesbc[ make_offset( var ) ].begin(); 
	 i != clausesbc[ make_offset( var ) ].end(); i++ ) {
      var2 = unmake_offset( *i );
#ifdef MODE_TEST
      if ( abs( var2 ) > num_vars ) critical_error( "STAR RULE: var out of range");
#endif
      if( unit_clauses[ make_offset( -var ) ] > 0 && unit_clauses[ make_offset( -var2 ) ] > 0 ) {
#ifdef DEBUG_ON      
        cout << "Applying SR to " << var << " " << var2 << endl;      
#endif
        fc++;
        //unit_clauses[ unit[ length++ ] = make_offset( -var ) ]--;
	unit_clauses[ make_offset( -var ) ]--;
	future_unit.push( make_offset( -var ) );
	length2++;
        //unit_clauses[ unit[ length++ ] = make_offset( -var2 ) ]--;
	unit_clauses[ make_offset( -var2 ) ]--;
	future_unit.push( make_offset( -var2 ) );
	length2++;
      }
    }

    for( BinaryClauseList::iterator i = clausesbc[ make_offset( -var ) ].begin(); 
      i != clausesbc[ make_offset( -var ) ].end(); i++ ) {
      var2 = unmake_offset( *i );
      if( unit_clauses[ make_offset( var ) ] > 0 && unit_clauses[ make_offset( -var2 ) ] > 0 ) {
#ifdef DEBUG_ON      
        cout << "Applying SR to " << -var << " " << var2 << endl;
#endif        
        fc++;
        //unit_clauses[ unit[ length++ ] = make_offset( var ) ]--;
	unit_clauses[ make_offset( var ) ]--;
	future_unit.push( make_offset( var ) );
	length2++;
        //unit_clauses[ unit[ length++ ] = make_offset( -var2 ) ]--;
	unit_clauses[ make_offset( -var2 ) ]--;
	future_unit.push( make_offset( -var2 ) );
	length2++;
      }
    }
  }
/*    
  while( index_clause < num_clauses ) {
    int& var1 = clauses[index_clause].penultimate_value_abs; 
    int& sense1 = clauses[index_clause].penultimate_literal;
    int& var2 = clauses[index_clause].max_value_abs_2;
    int& sense2 = clauses[index_clause].max_literal;
    if ( unit_clauses[ 2*var1 + !sense1 ] > 0 && unit_clauses[ var2 + !sense2 ] > 0 ) {
      fc++;
      unit_clauses[ unit[ length++ ] = (2*var1 + !sense1) ]--;
      unit_clauses[ unit[ length++ ] = (var2 + !sense2) ]--;
    }
    index_clause++;
  }
  */
#endif

#ifdef MODE_TEST
  if( fc < 0 ) {
#ifdef DEBUG_ON
    cout << "Binary Clauses" << endl;
    print_list( clausesbc, clausesbc + (2*num_vars+2), '\n' );    
#endif
    critical_error("FC < 0");
  }
#endif
#ifdef DEBUG_ON
  cout << "FC: " << fc << endl;;
#endif
  return fc;
}

void undo_forward_checking( int length ) {
  for( int i = 0; i < length; i++ ) {
    //unit_clauses[ unit[ i ] ]++;
    unit_clauses[ future_unit.top() ]++;
    future_unit.pop();
  }
}

bool final_clause_is_unsat( Clause& clause ) {
  for( int i = 0; i < clause.length; i++ )
    if ( solution[ abs( clause.literals[ i ] ) ] == TRUE or solution[ abs( clause.literals[ i ] ) ] == FALSE )
      if ( solution[ abs( clause.literals[ i ] ) ] == make_literal( clause.literals[ i ] ) )
	return false;
  return true;
}

bool verify_solution() {
  int unsat = 0;
  for( int i = 0; i < num_clauses; i++ )
    if ( final_clause_is_unsat( clauses[ i ] ) ) unsat++;
  return unsat == ub;
}

//
// Brach and Bound 
//

void solve_MaxSAT( int var, int index_clause, int unsat ) {
  int fc, gap;
  int length[] = {0, 0};
  //int unit[ MAX_VARS* 2 ], length_unit;
  int length_unit, length_star;

#ifdef DEBUG_ON
  cout << "DEBUG: Starting var " << var << " clause " << index_clause 
       << " and unsat " << unsat  << endl;
  int count = 0;
  for( int i = 1; i <= num_vars; i++ ) {
    count += unit_clauses[ 2*i+ TRUE ] + unit_clauses[ 2*i+FALSE ];
  }
  cout << "Number of unit clauses: " << count << endl;
  print_list( &partial_solution[1], &partial_solution[ num_vars+1 ], ' ' ); cout << endl;
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
    int fc = forward_checking( var, num_long_clauses, length_unit, length_star, unsat );
    unsat += fc;
    undo_forward_checking( length_unit+length_star );
    if ( unsat < ub ) {
#ifdef MODE_TEST
      if ( stop_point > unsat ) {
#ifdef DEBUG_ON
        cout << "unsat: " << unsat << endl;
	print_list( &partial_solution[1], &partial_solution[ num_vars+1 ], ' ' ); cout << endl;
#endif
        cout << "Stop point: " << stop_point << endl;
        critical_error( "Stop point reached" );
      }
#endif

      //!!
      /*
      //for( int c = num_clauses - 1, v = clauses[c].max_value_abs; clauses[c].max_value_abs == v; c-- ) {
      int literal, variable;
      for( variable = num_vars; clausesbc[ 2*variable+TRUE ].empty() or clausesbc[ 2*variable+FALSE ].empty(); variable-- );
      printf("Back to var: %d\n", variable );
      if ( partial_solution[ last_var-1 ] == TRUE ) literal = 2*last_var+TRUE;
      else literal = 2*last_var+FALSE;
	
      for( BinaryClauseList::iterator iter = clausesbc[ literal ].begin(); iter != clausesbc[ literal ].end(); iter++ ) {
	int v = *iter / 2;
	//int v = clauses[c].penultimate_value_abs;
	cout << "c Fixing " << v << endl;
	if ( unit_clauses[ 2*v+TRUE ] < unit_clauses[ 2*v+FALSE ] ) 
	  partial_solution[ v ] = FALSE;
	else
	  partial_solution[ v ] = TRUE;
      }
      */
      if ( unit_clauses[ 2*num_vars+TRUE ] < unit_clauses[ 2*num_vars+FALSE ] ) {
	partial_solution[ num_vars ] = FALSE;
#ifdef DEBUG_ON	
	cout << "Partial[" << var << "] = FALSE" << endl;
#endif
      }
      else {
	partial_solution[ num_vars ] = TRUE;
#ifdef DEBUG_ON
	cout << "Partial[" << var << "] = TRUE" << endl;
#endif
      }

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
  fc = forward_checking( var, new_index_clause, length_unit, length_star, unsat );
  //unsat += fc;
  //fc = 0;
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
    undo_forward_checking( length_unit+length_star );
#endif
    if( index_clause < num_long_clauses ) {
      back( var-1, index_clause );
    }
    return; 
  }

#ifdef UNIT_PROPAGATION
  if( unsat + 1 == ub ) {
    if ( unit_propagation( var ) ) {
      undo_unit_propagation( var );
#ifdef LOOK_AHEAD
      undo_forward_checking( length_unit+length_star );
#endif
      backtracks++;
      if( index_clause < num_long_clauses ) {
	back( var-1, index_clause );
      }
      return;
    }
  }
#endif

  check_clauses_bc( var, index_clause, length );

#ifdef LOOK_AHEAD
  gap = unit_clauses[ TRUE + 2*var ] - unit_clauses[ FALSE + 2*var ];
  undo_forward_checking( length_star );
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
      length[ TRUE ] + unit_clauses[ TRUE + 2*var ]
#endif 
      ) 
    {
      partial_solution[ var ] = TRUE; 
#ifdef DEBUG_ON
      cout << "Partial[" << var << "] = TRUE" << endl;
#endif
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
      length[ FALSE ] + unit_clauses[ FALSE + 2*var ]
#endif
      ) 
    {
      partial_solution[ var ] = FALSE;
#ifdef DEBUG_ON
      cout << "Partial[" << var << "] = FALSE" << endl;
#endif
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

#ifdef LOOK_AHEAD
  undo_forward_checking( length_unit );
#endif

  if( index_clause < num_long_clauses ) {
    back( var-1, index_clause );
  }
#ifdef UNIT_PROPAGATION
  undo_unit_propagation( var );
#endif
}

//
// Main
//

int main( int argc, char *argv[] ) {
#ifdef LOCAL_SEARCH
  ub = local_search( argv[1] ) + 1;
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
  ub = num_clauses;
  stop_point = atoi( argv[2] );
#else
#ifdef MANUAL_ORDERING
  ub = argc < 3 ? num_clauses : atoi( argv[ n ] );
#else
  ub = argc < 3 ? num_clauses : atoi( argv[ 2 ] );
#endif
#endif
#endif
  cout << "c Initial ub=" << ub << endl;
  backtracks = 0;
#ifdef RESOLUTION_RULE
  resolution_list = new list<ResolutionInfo>[ num_vars+1 ];
  unit_resolution_list = new UnitList[ num_vars+1 ];
#endif  

  //  if ( ub ) {
#ifdef VAR_MAPPING
    int mapping[ MAX_VARS ];
#endif

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

#ifdef VAR_MAPPING
    var_mapping( mapping );
#endif

    update_clause_max_value();  
    
    sort( clauses, clauses + num_clauses );

#ifdef DEBUG_ON    
    cout << "Starting clauses" << endl;
    print_list( clauses, clauses + num_clauses, '\n' );
#endif    

    create_binary_clause_db();

#ifdef DEBUG_ON    
    cout << "main: Clauses" << endl;
    print_list( clausesbc, clausesbc + (2*num_vars+2), '\n' );
    cout << "Long clauses" << endl;
    print_list( clauses, clauses + num_long_clauses, '\n' );
#endif    
#ifdef MODE_TEST
    check_runtime_error();
#endif    
#ifdef RESOLUTION_RULE
    resolution_rule_bc( 0 );    
#endif
    
    solve_MaxSAT( 0, 0, 0 );

#ifdef DEBUG_ON    
    cout << "main: Clauses" << endl;
    print_list( clausesbc, clausesbc + (2*num_vars+2), '\n' );
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

  //#ifdef DEBUG_ON
  //cout << "Solution" << endl;
  //print_list( &solution[1], &solution[num_vars+1], ' ' ); cout << endl;
  //cout << "Unmapped solution" << endl;

  /*
  if ( verify_solution() ) cout << "c Solution OK!" << endl;
  else cout << "c Solution NOT correct" << endl;

  
  int mapping[ MAX_VARS ];
  for( int i = 1; i <= num_vars; i++ ) {
    mapping[ i ] = find( var_map + 1, var_map + num_vars + 1, i ) - var_map;
  }
  */

  cout << "s OPTIMUM FOUND" << endl;
  cout << "v ";
  for( int i = 1; i <= num_vars; i++ ) {    
    if ( solution[ mapping[ i ] ] != UNDEF ) {
      if ( solution[ mapping[ i ] ] != TRUE ) cout << "-";
      cout << i << " ";
    }
  }
  cout << endl;
  
#ifdef DEBUG_ON
  cout << "c MAPPING: ";
  for( int i = 1; i <= num_vars; i++ )
    cout << var_map[ i ] << " ";    
  cout << endl;
  cout << "c NO MAPPING: ";
  for( int i = 1; i <= num_vars; i++ ) {
    if ( solution[ i ] != UNDEF ) {
      if ( solution[ i ] != TRUE ) cout << "-";
      cout << i << " ";
    }
  }
  cout << endl;
#endif
  
  return 0;
}
