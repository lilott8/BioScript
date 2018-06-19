-- MySQL dump 10.13  Distrib 5.7.16, for osx10.12 (x86_64)
--
-- Host: localhost    Database: chem_trails
-- ------------------------------------------------------
-- Server version	5.7.16

/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8 */;
/*!40103 SET @OLD_TIME_ZONE=@@TIME_ZONE */;
/*!40103 SET TIME_ZONE='+00:00' */;
/*!40014 SET @OLD_UNIQUE_CHECKS=@@UNIQUE_CHECKS, UNIQUE_CHECKS=0 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;

--
-- Table structure for table `reactive_groups`
--

DROP TABLE IF EXISTS `reactive_groups`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `reactive_groups` (
  `id` int(10) unsigned NOT NULL AUTO_INCREMENT,
  `name` varchar(100) DEFAULT NULL,
  `epa_id` int(10) NOT NULL,
  `other_id` int(10) DEFAULT NULL,
  PRIMARY KEY (`id`),
  UNIQUE KEY `epa_id_UNIQUE` (`epa_id`),
  UNIQUE KEY `id_UNIQUE` (`id`)
) ENGINE=InnoDB AUTO_INCREMENT=72 DEFAULT CHARSET=utf8;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `reactive_groups`
--

LOCK TABLES `reactive_groups` WRITE;
/*!40000 ALTER TABLE `reactive_groups` DISABLE KEYS */;
INSERT INTO `reactive_groups` VALUES (1,'Unknown',-1,NULL),(2,'Acids, Strong Non-oxidizing',1,NULL),(3,'Acids, Strong Oxidizing',2,NULL),(4,'Acids, Carboxylic',3,NULL),(5,'Alcohols and Polyols',4,NULL),(6,'Aldehydes',5,NULL),(7,'Amides and Imides',6,NULL),(8,'Amines, Phosphines, and Pyridines',7,NULL),(9,'Azo, Diazo, Azido, Hydrazine, and Azide Compounds',8,NULL),(10,'Carbamates',9,NULL),(11,'Bases, Strong',10,NULL),(12,'Cyanides, Inorganic',11,NULL),(13,'Thiocarbamate Esters and Salts/Dithiocarbamate Esters and Salts',12,NULL),(14,'Esters, Sulfate Esters, Phosphate Esters, Thiophosphate Esters, and Borate Esters',13,NULL),(15,'Ethers',14,NULL),(16,'Fluorides, Inorganic',15,NULL),(17,'Hydrocarbons, Aromatic',16,NULL),(18,'Halogenated Organic Compounds',17,NULL),(19,'Isocyanates and Isothiocyanates',18,NULL),(20,'Ketones',19,NULL),(21,'Sulfides, Organic',20,NULL),(22,'Metals, Alkali, Very Active',21,NULL),(23,'Metals, Elemental and Powder, Active',22,NULL),(24,'Metals, Less Reactive',23,NULL),(25,'Metals and Metal Compounds, Toxic',24,NULL),(26,'Diazonium Salts',25,NULL),(27,'Nitriles',26,NULL),(28,'Nitro, Nitroso, Nitrate, and Nitrite Compounds, Organic',27,NULL),(29,'Hydrocarbons, Aliphatic Unsaturated',28,NULL),(30,'Hydrocarbons, Aliphatic Saturated',29,NULL),(31,'Peroxides, Organic',30,NULL),(32,'Phenols and Cresols',31,NULL),(33,'Sulfonates, Phosphonates, and Thiophosphonates, Organic',32,NULL),(34,'Sulfides, Inorganic',33,NULL),(35,'Epoxides',34,NULL),(36,'Metal Hydrides, Metal Alkyls, Metal Aryls, and Silanes',35,NULL),(37,'Anhydrides',37,NULL),(38,'Salts, Acidic',38,NULL),(39,'Salts, Basic',39,NULL),(40,'Acyl Halides, Sulfonyl Halides, and Chloroformates',40,NULL),(41,'Organometallics',42,NULL),(42,'Oxidizing Agents, Strong',44,NULL),(43,'Reducing Agents, Strong',45,NULL),(44,'Non-Redox-Active Inorganic Compounds',46,NULL),(45,'Fluorinated Organic Compounds',47,NULL),(46,'Fluoride Salts, Soluble',48,NULL),(47,'Oxidizing Agents, Weak',49,NULL),(48,'Reducing Agents, Weak',50,NULL),(49,'Nitrides, Phosphides, Carbides, and Silicides',51,NULL),(50,'Chlorosilanes',55,NULL),(51,'Siloxanes',58,NULL),(52,'Halogenating Agents',59,NULL),(53,'Acids, Weak',60,NULL),(54,'Bases, Weak',61,NULL),(55,'Carbonate Salts',62,NULL),(56,'Alkynes, with Acetylenic Hydrogen',63,NULL),(57,'Alkynes, with No Acetylenic Hydrogen',64,NULL),(58,'Conjugated Dienes',65,NULL),(59,'Aryl Halides',66,NULL),(60,'Amines, Aromatic',68,NULL),(61,'Nitrate and Nitrite Compounds, Inorganic',69,NULL),(62,'Acetals, Ketals, Hemiacetals, and Hemiketals',70,NULL),(63,'Acrylates and Acrylic Acids',71,NULL),(64,'Phenolic Salts',72,NULL),(65,'Quaternary Ammonium and Phosphonium Salts',73,NULL),(66,'Sulfite and Thiosulfate Salts',74,NULL),(67,'Oximes',75,NULL),(68,'Polymerizable Compounds',76,NULL),(69,'Not Chemically Reactive',98,NULL),(70,'Insufficient Information for Classification',99,NULL),(71,'Water Reactive Substances',100,NULL);
/*!40000 ALTER TABLE `reactive_groups` ENABLE KEYS */;
UNLOCK TABLES;
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed on 2016-10-26 22:06:52
