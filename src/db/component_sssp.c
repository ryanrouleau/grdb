// Ryan Rouleau
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#include <limits.h> // For INT_MAX
#include <stdbool.h> // Cause I like using true/false instead of 1's and 0's #yolo
#include "graph.h"
#include "cli.h"

#define WEIGHT_MATRIX_SIZE 1000 // i.e. Max number of vertices expected in component


int
get_num_vertices(component_t c)
{

  /* based on component_print() in component.c */

  ssize_t size, len;
  char *buf;
  int readlen;

  assert(c != NULL);

  if (c->sv == NULL) size = 0;
  else size = schema_size(c->sv);

  readlen = sizeof(vertexid_t) + size;
  buf = malloc(readlen);

  int count = 0;
  for (off_t off = 0;; off += readlen) {
    lseek(c->vfd, off, SEEK_SET);
    len = read(c->vfd, buf, readlen);

    if (len <= 0) break;

    count++;

  }
  free(buf);

  return count;
}


void
populate_vertices_list(component_t c, vertexid_t *v_list)
{
  ssize_t size, len;
  char *buf;
  int readlen;
  vertexid_t v;

  if (c->sv == NULL) size = 0;
  else size = schema_size(c->sv);

  readlen = sizeof(vertexid_t) + size;
  buf = malloc(readlen);

  for (int i = 0, off = 0 ;; i++, off += readlen) {
    lseek(c->vfd, off, SEEK_SET);
    len = read(c->vfd, buf, readlen);
    if (len <= 0) break;
    v = *((vertexid_t *) buf);
    v_list[i] = v;
  }
  free(buf);
}


int
get_index_from_vertex_id(
        vertexid_t id,
        vertexid_t* v_list,
        int num_v)
{
  for (int i = 0; i < num_v; i++) {
    if (v_list[i] == id) {
      return i;
    }
  }
  return -1;
}


int
get_vertex_id_from_index(
        int index,
        vertexid_t* v_list,
        int num_v)
{
  // This func might be a bit too verbose... all well
  return v_list[index];
}


void
populate_edge_matrix(
        component_t c,
        int weights[WEIGHT_MATRIX_SIZE][WEIGHT_MATRIX_SIZE],
        vertexid_t *v_list,
        int num_v,
        char* attr)
{
  // indices in weight matrix match indices in v_list
  for (int i = 0; i < num_v; i++) {
    vertexid_t start = v_list[i];
    for (int j = 0; j < num_v; j++) {
      vertexid_t end = v_list[j];

      // Create an edge w/ vertices: start/end.  Used to get the real edge in the
      // component
      struct edge e;
      edge_t e1;
      edge_init(&e);
      edge_set_vertices(&e, start, end);

      e1 = component_find_edge_by_ids(c, &e);

      if (e1 == NULL) { // Edge does not exist -> set weight as INT_MAX
        weights[i][j] = INT_MAX;
      }
      else { // Edge exists -> set weight as the weight of the edge
        int offset = tuple_get_offset(e1->tuple, attr);
        int weight = tuple_get_int(e1->tuple->buf + offset);
        weights[i][j] = weight;
      }
    }
  }
}


attribute_t
get_int_tuple(attribute_t attr)
{

  // Return first attribute of type int i.e. the weight of the edge (frank
  // defines int type as 4 which is why curr_attr->bt tests against 4 instead of
  // int...)

  attribute_t curr_attr;
  for (curr_attr = attr; curr_attr != NULL; curr_attr = curr_attr->next) {
    if (curr_attr->bt == 4) return curr_attr;
  }
  return NULL;
}


bool
q_empty(
  vertexid_t *q,
  int num_v)
{
  for (int i = 0; i < num_v; i++) {
    if (q[i] != INT_MIN) {
      return false;
    }
  }
  return true;
}


int
get_index_with_min_dist(
  vertexid_t *q,
  int *dist,
  int num_v
)
{
  int min = INT_MAX;
  int min_index = -1;
  for (int i = 0; i < num_v; i++) {
    if (q[i] != INT_MIN && dist[i] < min) {
      min = dist[i];
      min_index = i;
    }
  }
  return min_index;
}


int
dijkstra(
        vertexid_t v1,
        vertexid_t v2,
        vertexid_t *v_list,
        int num_v,
        int *n,
        int *total_weight,
        vertexid_t **path,
        int weights[WEIGHT_MATRIX_SIZE][WEIGHT_MATRIX_SIZE])
{
  // init dijkstra auxiallary data structures
  vertexid_t *q = malloc(num_v * sizeof(vertexid_t));
  vertexid_t *prev = malloc(num_v * sizeof(vertexid_t));
  int *dist = malloc(num_v * sizeof(int));

  int v1_index = get_index_from_vertex_id(v1, v_list, num_v);

  vertexid_t NULL_vertex_id = -99999999;
  for (int i = 0; i < num_v; i++) { // for each vertex in graph
    vertexid_t curr_v = v_list[i];
    dist[i] = INT_MAX; // unknown dist from source to vertex i
    prev[i] = NULL_vertex_id;
    q[i] = curr_v;
  }
  dist[v1_index] = 0;

#if _DEBUG
  printf("v_list:\n");
  for (int i = 0; i < num_v; i++) {
    printf("index: %d, vertexid_t: %llu\n", i, v_list[i]);
  }
#endif
  int iters = 0;
  while (!q_empty(q, num_v) && iters < 100) { // main loop
    int u_index =  get_index_with_min_dist(q, dist, num_v); // vertex u in Q w/ min dist[u]
    q[u_index] = INT_MIN; // remove u from q
#if _DEBUG
    printf("v_index: %d, ", u_index);
    printf("v_list[v_index]: %llu\n", v_list[u_index]);
#endif
    // for each neighbor v of u where v has not been removed from q
    for (int v_index = 0; v_index < num_v; v_index++) {
      // neighbor since weight btwn is not infitiy, and not removed from q
      if (weights[u_index][v_index] != INT_MAX && q[v_index] != INT_MIN) {
        int alt_weight = dist[u_index] + weights[u_index][v_index];
        if (alt_weight < dist[v_index]) { // a short path to u has been found
          dist[v_index] = alt_weight;
          prev[v_index] = v_list[u_index];
        }
      }
    }
    iters++;
  }

#if _DEBUG
  for (int i = 0; i < num_v; i++) {
    printf("%llu -> %llu: %d weight\n", v1, v_list[i], dist[i]);
  }

  printf("prev:\n");
  for (int i = 0; i < num_v; i++) {
    printf("index: %d, prev[index]: %llu\n", i, prev[i]);
  }
#endif

  // reconstruct path to get the length of it
  int u_index = get_index_from_vertex_id(v2, v_list, num_v);
  *n = 0;
  while(prev[u_index] != NULL_vertex_id) {
    if ((*n) == 50000) return -1; // exit w/ error code if infinite loop
    (*n)++;
    u_index = get_index_from_vertex_id(prev[u_index], v_list, num_v);
  }
  (*n)++;

#if _DEBUG
  printf("path n: %d\n", *n);
#endif

  // now we know how big to make the array holding the path
  vertexid_t* path_local = malloc((*n) * sizeof(vertexid_t));
  int current_i = (*n) - 1;
  u_index = get_index_from_vertex_id(v2, v_list, num_v);
  while(prev[u_index] != NULL_vertex_id) {
    path_local[current_i] = v_list[u_index];
    current_i--;
    u_index = get_index_from_vertex_id(prev[u_index], v_list, num_v);
  }
  path_local[current_i] = v1;

#if _DEBUG
  printf("PATH:\n");
  for (int i = 0; i < (*n); i++) {
    printf("%llu -> ", path_local[i]);
  }
  printf("\n");
#endif

  *path = path_local;
  *total_weight = dist[get_index_from_vertex_id(v2, v_list, num_v)];

  free(q);
  free(prev);
  free(dist);
  free(path_local);

  return 1; // good exit code
}


int
component_sssp(
        component_t c,
        vertexid_t v1,
        vertexid_t v2,
        int *n,
        int *total_weight,
        vertexid_t **path)
{
  // Set files in component so we can get vertice and edge info from the files.
  // gno and cno are defined in cli.h
  c->vfd = vertex_file_init(gno, cno);
  c->efd = edge_file_init(gno, cno);

  // Get the number of vertices in the component and create a list that holds
  // all the vertex id's.
  int num_v = get_num_vertices(c);
  vertexid_t *v_list = malloc(num_v * sizeof(vertexid_t));
  populate_vertices_list(c, v_list);

  // init matrix which will hold weights of edges
  int weights[WEIGHT_MATRIX_SIZE][WEIGHT_MATRIX_SIZE];

  // Get the atrribute name of weight so we can get the weight of the edge from
  // edge tuple in populate_edge_matrix()
  attribute_t weight_attr;
  weight_attr = get_int_tuple(c->se->attrlist);

  populate_edge_matrix(c, weights, v_list, num_v, weight_attr->name);

  // At this point: weights is a 2d array that holds weights between vertices.
  // The indices do not correspond to vertex id's -> An index corresponds to the
  // same index in v_list (the list of vertex_id's).

  // Ensure v1 and v2 are in the component, if either one is not: return -1 and
  // print an error msg to user
  bool v1_in_graph = false;
  bool v2_in_graph = false;
  for (int i = 0; i < num_v; i++) {
    if (v1 == v_list[i])
      v1_in_graph = true;
    if (v2 == v_list[i])
      v2_in_graph = true;
  }
  if (!v1_in_graph) {
    printf("The starting vertex %llu is not in the component.\n", v1);
    return -1;
  }
  else if (!v2_in_graph) {
    printf("The ending vertex %llu is not in the component.\n", v2);
    return -1;
  }

  int dijkstra_exit_code = dijkstra(v1, v2, v_list, num_v, n, total_weight, path, weights);

	/* Change this as needed */
	return dijkstra_exit_code;
}
