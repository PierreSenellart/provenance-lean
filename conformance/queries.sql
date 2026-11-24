-- name: rel_dups
SELECT x FROM t;
-- name: sel_eq
SELECT x FROM t WHERE x = 1;
-- name: sel_not_eq
SELECT x FROM t WHERE NOT (x = 1);
-- name: sel_is_null
SELECT x FROM t WHERE x IS NULL;
-- name: proj_add
SELECT x + 1 FROM t;
-- name: union_all
SELECT x FROM t UNION ALL SELECT x FROM s;
-- name: distinct
SELECT DISTINCT x FROM t;
-- name: except_set
SELECT x FROM t EXCEPT SELECT x FROM s;
-- name: diff_keeps_dups
SELECT x FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.x IS NOT DISTINCT FROM t.x);
-- name: intersect_set
SELECT x FROM t INTERSECT SELECT x FROM s;
-- name: join_eq
SELECT t.x, s.x FROM t, s WHERE t.x = s.x;
-- name: group_aggs
SELECT dept, count(*), count(sal), sum(sal), min(sal), max(sal) FROM emp GROUP BY dept;
-- name: scalar_agg_empty
SELECT count(*), sum(sal) FROM emp WHERE id > 1000;
-- name: left_join_null_keys
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d LEFT JOIN emp e ON e.dept = d.d;
-- name: not_in_null
SELECT d, name FROM dept WHERE d NOT IN (SELECT dept FROM emp);
-- name: not_in_no_null
SELECT d, name FROM dept WHERE d NOT IN (SELECT dept FROM emp WHERE id < 103);
-- name: rank_ties_nulls
SELECT id, dept, sal, rank() OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
-- name: exists_semi
SELECT d, name FROM dept WHERE EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d);
-- name: not_exists_anti
SELECT d, name FROM dept WHERE NOT EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d);
-- name: in_sub
SELECT d, name FROM dept WHERE d IN (SELECT dept FROM emp);
-- name: right_join_null_keys
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d RIGHT JOIN emp e ON e.dept = d.d;
-- name: full_join_null_keys
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d FULL JOIN emp e ON e.dept = d.d;
-- name: dense_rank_ties_nulls
SELECT id, dept, sal, dense_rank() OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
-- name: win_sum_partition
SELECT id, dept, sal, sum(sal) OVER (PARTITION BY dept) FROM emp;
-- name: win_running_count
SELECT id, dept, sal, count(*) OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
-- name: limit_key
SELECT id, dept, sal FROM emp ORDER BY id LIMIT 2;
-- name: fetch_with_ties
SELECT id, dept, sal FROM emp ORDER BY sal DESC NULLS LAST FETCH FIRST 1 ROWS WITH TIES;
-- name: values_rows
SELECT * FROM (VALUES (1,2),(1,2),(3,NULL::int)) v;
-- name: lateral_apply
SELECT d.d, d.name, e.id FROM dept d, LATERAL (SELECT id FROM emp WHERE emp.dept = d.d) e;
-- name: group_no_agg
SELECT dept FROM emp GROUP BY dept;
-- name: proj_case
SELECT CASE WHEN x = 1 THEN 10 ELSE 20 END FROM t;
-- name: proj_coalesce
SELECT COALESCE(x, 7) FROM t;
-- name: proj_mul_add
SELECT x * 2 + x FROM t;
-- name: agg_filter
SELECT dept, count(*) FILTER (WHERE sal >= 90) FROM emp GROUP BY dept;
-- name: agg_distinct
SELECT dept, count(DISTINCT sal) FROM emp GROUP BY dept;
-- name: scalar_agg_distinct
SELECT sum(DISTINCT sal) FROM emp;
-- name: having_count
SELECT dept FROM emp GROUP BY dept HAVING count(*) >= 2;
-- name: having_sum
SELECT dept FROM emp GROUP BY dept HAVING sum(sal) > 100;
-- name: where_on_agg
SELECT dept, c FROM (SELECT dept, count(*) AS c FROM emp GROUP BY dept) g WHERE c = 2;
-- name: scalar_subquery_max
SELECT d, name, (SELECT max(sal) FROM emp WHERE emp.dept = dept.d) FROM dept;
-- name: scalar_subquery_count
SELECT d, name, (SELECT count(*) FROM emp WHERE emp.dept = dept.d) FROM dept;
-- name: lag_key
SELECT id, dept, sal, lag(sal) OVER (ORDER BY id) FROM emp;
-- name: lead_key
SELECT id, dept, sal, lead(sal) OVER (ORDER BY id) FROM emp;
-- name: first_value_part
SELECT id, dept, sal, first_value(sal) OVER (PARTITION BY dept ORDER BY id) FROM emp;
-- name: row_number_key
SELECT id, dept, sal, row_number() OVER (PARTITION BY dept ORDER BY id) FROM emp;
-- name: limit_offset
SELECT id, dept, sal FROM emp ORDER BY id LIMIT 2 OFFSET 1;
-- name: distinct_on
SELECT DISTINCT ON (dept) id, dept, sal FROM emp ORDER BY dept, id;
-- name: lag_part
SELECT id, dept, sal, lag(sal) OVER (PARTITION BY dept ORDER BY id) FROM emp;
-- name: last_value_part
SELECT id, dept, sal, last_value(sal) OVER (PARTITION BY dept ORDER BY id RANGE BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING) FROM emp;
-- name: lag_two
SELECT id, dept, sal, lag(sal, 2) OVER (ORDER BY id) FROM emp;
