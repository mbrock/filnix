-- The gate's SQLite workload (docs/perf.md): an in-memory database, so
-- every run starts empty, with the kinds of work tests/sqlite/workload.sql
-- covers at sizes that take filcc's build about half a second.
-- Deterministic: nothing reads the clock or a random source.
.bail on
.headers on
create table customer(id integer primary key, name text not null, city text, joined text);
create table item(id integer primary key, title text, price real, weight real);
create table orders(id integer primary key, customer integer, item integer, qty integer, placed text);

with recursive n(i) as (select 1 union all select i + 1 from n where i < 5000)
insert into customer(name, city, joined)
select printf('customer-%06d', i),
       case i % 7 when 0 then 'Oslo' when 1 then 'Lima' when 2 then 'Pune'
                  when 3 then 'Kyiv' when 4 then 'Quito' when 5 then 'Accra' else 'Hanoi' end,
       date('2020-01-01', printf('+%d days', (i * 37) % 1500))
from n;

with recursive n(i) as (select 1 union all select i + 1 from n where i < 2000)
insert into item(title, price, weight)
select 'item ' || hex(zeroblob(i % 5)) || i, round(i * 1.37 + (i % 13) / 7.0, 2), i / 3.0 from n;

with recursive n(i) as (select 1 union all select i + 1 from n where i < 50000)
insert into orders(customer, item, qty, placed)
select 1 + (i * 7919) % 5000, 1 + (i * 104729) % 2000, 1 + i % 9,
       datetime('2023-03-01 08:00:00', printf('+%d minutes', i * 53))
from n;

create index orders_customer on orders(customer, placed);
create index orders_item on orders(item);
create unique index customer_name on customer(name);

-- Joins and aggregates.
select c.city, count(*) as orders, round(sum(o.qty * i.price), 2) as total,
       round(avg(i.price), 4) as mean_price, max(o.placed) as last
from orders o join customer c on c.id = o.customer join item i on i.id = o.item
group by c.city order by total desc;

-- Windows over the joined rows.
select city, name, spent, rank from (
  select c.city, c.name, round(sum(o.qty * i.price), 2) as spent,
         rank() over (partition by c.city order by sum(o.qty * i.price) desc, c.name) as rank
  from orders o join customer c on c.id = o.customer join item i on i.id = o.item
  group by c.id)
where rank <= 3 order by city, rank;

-- Index lookups in a correlated subquery.
select count(*), sum(n) from (
  select (select count(*) from orders o where o.customer = c.id and o.placed >= '2024-01-01') as n
  from customer c);

-- Strings, printf and JSON.
select length(group_concat(printf('%s:%08.3f', title, price * 1.0001), ',')) from item;
select json_extract(j, '$.n'), json_array_length(j, '$.xs') from (
  select json_object('n', count(*), 'xs', json_group_array(qty)) as j from orders where item % 97 = 1);

-- Updates and deletes through indexes.
update orders set qty = qty + 1 where customer % 13 = 0;
delete from orders where item % 17 = 0;
select count(*), sum(qty) from orders;

-- Full-text search.
create virtual table notes using fts5(body);
with recursive n(i) as (select 1 union all select i + 1 from n where i < 5000)
insert into notes(body)
select printf('order %d for %s ships %s with %d units', i,
              (select name from customer where id = 1 + i % 5000),
              case i % 3 when 0 then 'early' when 1 then 'late' else 'today' end, i % 9)
from n;
select count(*) from notes where notes match 'late AND units';
select count(*) from notes where notes match '"ships today"';

-- Sorting without an index.
select sum(rowid % 1000) from (select rowid from orders order by placed desc, qty, customer limit 12000);
