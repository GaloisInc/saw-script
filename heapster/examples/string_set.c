#include <stdlib.h>
#include <stdint.h>

struct string;
typedef struct string string;

struct string_set;
typedef struct string_set string_set;

extern string_set *string_set_empty ();
extern void string_set_insert (string_set *set, string *str);
extern void string_set_remove (string_set *set, string *str);

void insert_remove (string_set *set, string *str1, string *str2) {
  string_set_insert (set, str1);
  string_set_remove (set, str2);
}
