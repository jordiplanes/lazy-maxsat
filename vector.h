
template<class T, int __MAX = 55>
struct vector {
  T items[ __MAX ];
  int length;
  typedef T* iterator;
  vector() { length = 0; }
  void push( T item ) {
#ifdef MODE_TEST
   if ( length == __MAX ) { printf("Critical error in stack\n"); exit(-1); }
#endif
   items[ length++ ] = item; //!! items[++length]=item
  }
  void push_back( T item ) { push( item ); }
  void pop() {
    --length;
  }
  void pop_back() { pop(); }
  T& top() {
    return items[ length-1 ]; //!! items[length]
  }
  int size() {
    return length;
  }
  bool empty() {
     return length==0;
  }
  T* begin() {
     return &items[0];
  }
  T* end() {
     return &items[ length ];
  }
  void erase( iterator begin, iterator end ) {
     for( iterator i = begin; i < end; i++ ) {
        *i = *(end+(i-begin));
     }
  }
};

