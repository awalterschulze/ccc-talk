/*
 * This file was generated by the Gradle 'init' task.
 *
 * This is a general purpose Gradle build.
 * Learn more about Gradle by exploring our samples at https://docs.gradle.org/7.4.2/samples
 * This project uses @Incubating APIs which are subject to change.
 */

import org.gradle.api.tasks.testing.logging.TestLogEvent

plugins {
    id("org.jetbrains.kotlin.jvm") version "1.6.21"
    `java-library`
}

repositories {
    mavenCentral() 
}

dependencies {
    implementation(platform("org.jetbrains.kotlin:kotlin-bom"))
    implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
    testImplementation(kotlin("test"))
    testImplementation("net.jqwik:jqwik:1.6.5")
    testImplementation("net.jqwik:jqwik-kotlin:1.6.5")
    testImplementation("org.assertj:assertj-core:3.22.0")
}


tasks.withType<org.jetbrains.kotlin.gradle.tasks.KotlinCompile> {
    kotlinOptions {
        freeCompilerArgs = listOf(
            "-Xjsr305=strict", // Strict interpretation of nullability annotations in jqwik API
            "-Xemit-jvm-type-annotations" // Enable nnotations on type variables
        )
        jvmTarget = "11" // 1.8 or above
        javaParameters = true // Get correct parameter names in jqwik reporting
    }
}

tasks {
    test {
        useJUnitPlatform {
            includeEngines("jqwik", "junit-jupiter")
        }
        include("**/*Properties.class")
        include("**/*Examples.class")
        include("**/*Test.class")
        include("**/*Tests.class")

        dependsOn("cleanTest")
        testLogging {
            showStandardStreams = true
            events(
                org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED,
                org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED,
                org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED,
            )
        }
    }
}
