
template<class T, int __MAX = 55>
struct stack {
  T items[ __MAX ];
  int length;
  stack() { length = 0; }
  void push( T item ) {
   items[ length++ ] = item; //!! items[++length]=item
  }
  void pop() {
    --length;
  }
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
};

