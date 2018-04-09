# Kirk Boyer, 2016-2018
# In our paper "Extremal Problems on Ray Sensor Configurations" we construct
# a vertex-weighted, edge-labeled graph and use it to prove some results. To do
# this we make use of the maximal independent vertex sets with certain total 
# vertex weights, and to compute cases to address in our proof, we used this code.
# 
# Some code is entirely commented out. This code is peripheral, and left here
# in comments for reference.

require(igraph)


# DEFINE FUNCTIONS
# ============================================================
# function to get the complement (as sets) of a set of vertices of a given graph
get.vertex.set.complement <- function(graph, vxs){ V(graph)[!(V(graph)$name %in% vxs$name)] }

# function to compute the weight of a set of vertices
vx.set.weight <- function(s){ sum(s$weight) }


# BUILD GRAPHS
# ============================================================
# Initialize the graph "g", which is the same as G_\alpha in the paper.
g <- make_empty_graph(n=12)
V(g)$name <- c('p1', 'p2', 'p3', 'p4', 'q1', 'q2', 'q3', 'q4', 'm1', 'm2', 'm3', 'm4')

# Edges of g are imported from a csv containing the adjacencies proved in the paper.
# (make sure g_n_2_adj_matrix.csv is in the working directory to make this work)
adjacencies <- read.csv("g_n_2_adj_matrix.csv") names(adjacencies) <- V(g)$name
# Put those edges into the graph g
for (i in 1:12){
  for (j in 1:12){
    if (adjacencies[[i]][[j]] == 1){
      g <- add_edges(g, V(g)$name[c(i, j)], edge_type="half")
    } else if (adjacencies[[i]][[j]] == 2){
      g <- add_edges(g, V(g)$name[c(i, j)], edge_type="complete")
    }
  }
}

# make g undirected (collapse mode means no double edges)
g <- as.undirected(g, mode="collapse", edge.attr.comb="max")
n <- length(V(g))

# edges q3-m1 and q1-m3 are actually complete in the union, because the order in which the
# half graphs unfold are opposite in G_TB and G_AB for these edges
# UPDATE: Changed adjacency matrix to reflect this info. Don't need to change here.
# E(g)["q3" %--% "m1"]$edge_type <- "complete"
# E(g)["q1" %--% "m3"]$edge_type <- "complete"


# Set alpha (angle from 0 to pi normalized to be from 0 to 1)
alpha <- 0.5

# Set G_alpha vertex weights according to proportion of rays in each group 
base_weight = 1

# Set vertex weights based on the construction and choice of alpha.
V(g)[c('p1', 'q1', 'p3', 'q3')]$weight <- base_weight * alpha
V(g)[c('m1', 'm3')]$weight <- base_weight * 2 * alpha
V(g)[c('p2', 'p4', 'q2', 'q4')]$weight <- base_weight * (1 - alpha)
V(g)[c('m2', 'm4')]$weight <- base_weight * 2 * (1 - alpha)

total_weight <- vx.set.weight(V(g))

# Set vertex colors and sizes for visualizing the graph.
V(g)$color <- "white"
base_size <- 25
V(g)$size <- base_size
V(g)[c('p2', 'p4', 'q2', 'q4')]$size <- 2*base_size
V(g)[c('m1', 'm3')]$size <- 1.5*base_size
V(g)[c('m2', 'm4')]$size <- 2.5*base_size

# Set edge colors and sizes for visualizing the graph
E(g)$color <- "black"
E(g)$color[which(E(g)$edge_type == "half")] <- "blue"
E(g)$width <- 1
E(g)$width[which(E(g)$edge_type == "half")] <- 3


# Get subgraph G^c. It's the subgraph of G_alpha induced by the "complete" edges
cg <- delete_edges(g, edges=E(g)[E(g)$edge_type != "complete"])

# Get Maximal Independent vertex Sets in G^c 
cg_maximal_ivs <- maximal_ivs(cg)                           # maximal, not max-weight
cg_maximal_ivs_weights <- sapply(cg_maximal_ivs, vx.set.weight) # get list of weights

# Pare down to maximal-IVSs that have total weight > n/4, since only (complements of) these 
#  are small vx covers (< 3n/4, the target bound) and need further checking in half edges
cg_big_maximal_ivs <- cg_maximal_ivs[cg_maximal_ivs_weights > total_weight/4]

# Get the vertex sets inducing subgraphs of G^h with vertices in each large enough maximal IVS
cg_big_maximal_ivs_vertices <- sapply(cg_big_maximal_ivs, 
                                       function(vertex_set)
                                       {
                                           vertex_set$name
                                       })

# extract these subgraphs from G^h
hg <- delete_edges(g, edges=E(g)[E(g)$edge_type != "half"])
hg_subgraphs <- list()
for (i in 1:length(cg_big_maximal_ivs_vertices)){
  sg <- induced_subgraph(hg, cg_big_maximal_ivs_vertices[[i]])
  #V(sg)$label <- NA
  hg_subgraphs[[i]] <- sg
}

# remove isolated vertices from each subgraph
for (i in 1:length(hg_subgraphs)){
  #hg_subgraphs[[i]] <- delete.vertices(hg_subgraphs[[i]], degree(hg_subgraphs[[i]]) < 1)
}

# hg_subgraphs[1,2,3,4,5] = [c,a,b,e,d]
# [a,b,c,d,e] = hg_subgraphs[2,3,1,5,4]
# p1, q1, p3, q3			alpha
# m1, m3				      2alpha
# p2, p4, q2, q4			(1-alpha)
# m2, m4				      2(1-alpha)

# wt (out of 8) of **complement** of.
#  [1]: p4 q1 q3 m1 m3 m4: (1-a)+a+a+2a+2a+2(1-a) = 3(1-a)+6a              = 3 + 3a
#           So, wt. to cover is 6 - 3 - 3a      = ((((  3 + 3a  ))))
#  [2]: p4 q1 q2 q4 m1 m2 m4: (1-a)+a+(1-a)+(1-a)+2a+4(1-a) = 7(1-a)+3a    = 7 - 4a
#           So, wt. to cover is 6 - 7 + 4a      = ((((  -1 + 4a  ))))
#  [3]: p2 p4 q3 m2 m3 m4: (1-a)+(1-a)+a+2(1-a)+2a+2(1-a) = 6(1-a)+3a      = 6 - 3a
#           So, wt. to cover is 6 - 6 + 3a      = ((((  3a  ))))
#  [4]: p2 p4 q1 q3 m3 m4: (1-a)+(1-a)+a+a+2a+2(1-a) = 4(1-a)+4a           = 4
#           So, wt. to cover is 6 - 4           = ((((  2  ))))
#  [5]: p1 p2 p3 q3 m1 m2 m3: a+(1-a)+a+a+2a+2(1-a)+2a = 7a + 3(1-a)       = 3 + 4a
#           So, wt. to cover is 6 - 3 - 4a      = ((((  3 - 4a  ))))


# g_names_and_weights <- as.data.frame(t(matrix(c(V(g)$name, V(g)$weight), ncol=2)))
# gnw <- g_names_and_weights

# print the weights for the independent vertex sets
print(cg_maximal_ivs_weights[cg_maximal_ivs_weights > total_weight/4])
print(length(hg_subgraphs))
print(length(cg_maximal_ivs))


# tkplot
for (sg in hg_subgraphs){
  V(sg)$label.cex <- 3 # label font size
  tkplot(sg)
}
