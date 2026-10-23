// error: _Generic has duplicate compatible associations
typedef int integer;
int x = _Generic(0, int: 1, integer: 2);
